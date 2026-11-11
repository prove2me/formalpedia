-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_comparison_inequality
-- name    : BlottoFPTAS.Main.comparison_inequality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:51.037232+00:00
-- url     : https://prove2.me/theorems/dfd22b7a-75c5-4739-a738-bdf506ec6a70
-- title:
--   §5.2, comparison inequality — f(x, σ) − f(π, y) ≤ f(p̃, σ) − f(π, q̃) + d(p̃, x) + d(q̃, y) ≤ R + 2β_opt
-- statement:
--   Let $X,Y$ be finite sets of code allocations, and let $p_t,q_t$ (auxiliary marginals), $\lambda_t,\mu_t$ (signed multipliers), $x_t\in X$, $y_t\in Y$ for $t=1,\dots,T$ satisfy Parts 1–2 of Lemma 5.7 with numbers $R,\beta_{\mathrm{opt}}\ge0$: for all fixed comparison families, the four average regrets of the update table (p. 37; $p$: $f(p,q_t)+\lambda_t\cdot F_p$ minimized; $q$: $f(p_t,q)-\mu_t\cdot F_q$ maximized; $\lambda$: $\lambda\cdot(F_{p_t}-F_{x_t})$ maximized; $\mu$: $\mu\cdot(F_{q_t}-F_{y_t})$ maximized) sum to at most $R$, and $\lambda_t\cdot F_{x_t}\ge\max_{x\in X}\lambda_t\cdot F_x-\beta_{\mathrm{opt}}$, $\mu_t\cdot F_{y_t}\ge\max_{y\in Y}\mu_t\cdot F_y-\beta_{\mathrm{opt}}$. Let $x$, $y$ be the uniform distributions on the lists $(x_t)$, $(y_t)$ and $\tilde p=T^{-1}\sum_tp_t$, $\tilde q=T^{-1}\sum_tq_t$. Then for every distribution $\pi$ on $X$ and $\sigma$ on $Y$,
--   $$f(x,\sigma)-f(\pi,y)\le f(\tilde p,\sigma)-f(\pi,\tilde q)+d_{\hat v}(\tilde p,x)+d_{\hat v}(\tilde q,y)\le R+2\beta_{\mathrm{opt}}.$$
--   With Lemma 5.7's $R+2\beta_{\mathrm{opt}}<z/64$ this is the paper's $<z/64$: $(x,y)$ is a $z/64$-Nash equilibrium of the game restricted to $X$ and $Y$.
--
--   Differences from the source:
--   - generalization: the sequences produced by the Appendix D implementation, with R + 2β_opt < z/64 (Lemma 5.7), conclusion < z/64 → any sequences satisfying Parts 1–2 of Lemma 5.7 with numbers R, β_opt ≥ 0, conclusion ≤ R + 2β_opt; reason: Lemma 5.7 is not formalized; its Parts 1–2 are exactly these hypotheses and R + 2β_opt < z/64 recovers the printed bound
--   - generalization: X, Y the candidate and response allocations, codes in I = {0, …, 2^Λ − 1} → any finite sets of code allocations over {0, …, N − 1}; reason: the argument uses only finiteness of X and Y
--   - encoding: f and d_v̂ evaluated on allocations and distributions through their marginals → fPay and dW applied to margOf/cdfDistr of the distributions; reason: the paper's own convention (p. 36)
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), pp. 39–40, §5.2, proof of Lemma 5.6 (comparison inequality)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Learning

namespace BlottoFPTAS.Main

/-- **§5.2, proof of Lemma 5.6, comparison inequality** (Bichler, Ghosh, arXiv:2611.05221, held
version sha256 cac3638e…, pp. 39–40). Let `X`, `Y` be finite sets of code allocations, and let
`p_t, q_t` (auxiliary marginals), `λ_t, μ_t` (signed multipliers), `x_t ∈ X`, `y_t ∈ Y`,
`t < T`, satisfy Parts 1–2 of Lemma 5.7 with numbers `R, β_opt ≥ 0`: for all comparison families
the four average regrets (computed with the exact objectives of the update table, p. 37) sum to
at most `R`, and every `x_t`, `y_t` maximizes `λ_t · F_x` over `X`, `μ_t · F_y` over `Y`, up to
`β_opt`. Let `x̄`, `ȳ` be the uniform distributions on the two lists and `p̃`, `q̃` the averaged
auxiliary marginals. Then for all distributions `π` on `X` and `σ` on `Y`,
`f(x̄, σ) − f(π, ȳ) ≤ f(p̃, σ) − f(π, q̃) + d(p̃, x̄) + d(q̃, ȳ) ≤ R + 2β_opt`
(the paper's `< z/64` is the case `R + 2β_opt < z/64`). -/
theorem comparison_inequality {m N T : ℕ} (hN : 0 < N) (hT : 0 < T) (w : Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1)
    (Xs Ys : Finset (Fin m → Fin N))
    (p q : Fin T → Fin m → Fin N → ℝ) (lam mu : Fin T → Fin m → Bool × Fin N → ℝ)
    (xs ys : Fin T → Fin m → Fin N)
    (hp : ∀ t, IsAux (p t)) (hq : ∀ t, IsAux (q t))
    (hlam : ∀ t, IsMult (lam t)) (hmu : ∀ t, IsMult (mu t))
    (hxs : ∀ t, xs t ∈ Xs) (hys : ∀ t, ys t ∈ Ys)
    (R βopt : ℝ) (hR : 0 ≤ R) (hβ : 0 ≤ βopt)
    (hPart1 : ∀ (p' q' : Fin m → Fin N → ℝ) (lam' mu' : Fin m → Bool × Fin N → ℝ),
      IsAux p' → IsAux q' → IsMult lam' → IsMult mu' →
      (∑ t, ((fPay w (p t) (q t) + pair w (lam t) (cdfAux (p t))) -
          (fPay w p' (q t) + pair w (lam t) (cdfAux p')))) / T +
      (∑ t, ((fPay w (p t) q' - pair w (mu t) (cdfAux q')) -
          (fPay w (p t) (q t) - pair w (mu t) (cdfAux (q t))))) / T +
      (∑ t, (pair w lam' (fun j a => cdfAux (p t) j a - cdfAlloc (xs t) j a) -
          pair w (lam t) (fun j a => cdfAux (p t) j a - cdfAlloc (xs t) j a))) / T +
      (∑ t, (pair w mu' (fun j a => cdfAux (q t) j a - cdfAlloc (ys t) j a) -
          pair w (mu t) (fun j a => cdfAux (q t) j a - cdfAlloc (ys t) j a))) / T ≤ R)
    (hPart2x : ∀ t, ∀ x ∈ Xs, pair w (lam t) (cdfAlloc x) ≤ pair w (lam t) (cdfAlloc (xs t)) + βopt)
    (hPart2y : ∀ t, ∀ y ∈ Ys, pair w (mu t) (cdfAlloc y) ≤ pair w (mu t) (cdfAlloc (ys t)) + βopt) :
    ∀ π σ : (Fin m → Fin N) → ℝ, IsDist π → (∀ x, x ∉ Xs → π x = 0) →
      IsDist σ → (∀ y, y ∉ Ys → σ y = 0) →
      fPay w (margOf (listDist xs)) (margOf σ) - fPay w (margOf π) (margOf (listDist ys)) ≤
          fPay w (avgAux p) (margOf σ) - fPay w (margOf π) (avgAux q) +
            dW w (cdfAux (avgAux p)) (cdfDistr (listDist xs)) +
            dW w (cdfAux (avgAux q)) (cdfDistr (listDist ys)) ∧
        fPay w (avgAux p) (margOf σ) - fPay w (margOf π) (avgAux q) +
            dW w (cdfAux (avgAux p)) (cdfDistr (listDist xs)) +
            dW w (cdfAux (avgAux q)) (cdfDistr (listDist ys)) ≤ R + 2 * βopt := by sorry

end BlottoFPTAS.Main
