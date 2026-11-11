-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_6_1
-- name    : DataDepProb.Discrete.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:13:07.894003+00:00
-- url     : https://prove2.me/theorems/7b02fb9e-c55a-44a5-b6b5-b9cc2d92b2a0
-- title:
--   Lemma 6.1 — penalized multiplicative weights: $\eta\ell_t\le K_t-K_{t+1}+\eta^2/32+\lambda\beta^2+2\delta_n\beta+\delta_n^2/\lambda\,(+\tau)$
-- statement:
--   Let $n\ge1$, $\eta,\lambda>0$ and $\beta\ge0$. Suppose each $P_s$ ($s\in[d]^n$) is continuously differentiable and convex on a neighborhood of $\tilde\Delta_d$, is nonnegative on $\tilde\Delta_d$, vanishes at $e_s$, and satisfies (12): for every $D\in\Delta_d$,
--   $$\mathrm{KL}(p\|q)^2\le P_s(p)+P_s(q)\quad(p,q\in\tilde\Delta_d),\qquad E_{S\sim D^n}P_S(\tilde D)\le\beta^2 .$$
--   Let $\mathcal G:[d]^n\to[0,1]^{[d]}$ and consider recursion (8) with the penalized update $U_s$ of (14). For every $D\in\Delta_d$ and $t\ge0$,
--   $$\eta\ell_t\le K_t-K_{t+1}+\frac{\eta^2}{32}+\lambda\beta^2+2\delta_n\beta+\frac{\delta_n^2}\lambda .\qquad(15)$$
--   For $\tau\ge0$, the bound also holds with an additional $\tau$ if each update returns $v\in\tilde\Delta_d$ satisfying $\max_{w\in\tilde\Delta_d}\langle\log(v/q^+)+\lambda\nabla P_s(v),v-w\rangle\le\tau$.
--
--   Summed over $t$, (15) bounds the average squared error of the procedure; it is the main technical lemma behind Theorem 1.1.
--
--   Differences from the source:
--   - encoding: $n$ implicit → hypothesis $1\le n$; reason: amplification is undefined for $n=0$.
--   - encoding: the randomness of $q_t(s)$ → $q_t(s)$ is a function of $t$ independent uniform amplification coins and $K_t,\ell_t$ are finite averages over $S\sim D^n$ and the coins; reason: the run's randomness is exactly its amplification coins.
--   - encoding: "a neighborhood of $\tilde\Delta_d$", $\nabla P_s(v)$ → an open set $U\supseteq\tilde\Delta_d$ with `ContDiffOn ℝ 1` and `ConvexOn ℝ U`; the pairing with $v-w$ is `fderiv ℝ (P s) v (v - w)`; reason: Lean calculus conventions.
--   - reading: "each update returns $v$ satisfying" the gap condition → any update rule `U` with the gap condition for every $s$ and every $q\in\tilde\Delta_d$, $f\in[0,1]^{[d]}$, $b\in[0,1]$; reason: these are the only inputs a run presents to the update.
--   - reading: the exact update $U_s$ → the minimizer selected by `Classical.epsilon` (`exactUpdate`); reason: it exists and is unique under the hypotheses.
--   - reading: the query mapping of the recursion → an arbitrary `G` with values in $[0,1]$, universally quantified; reason: the lemma holds for the estimator's $\mathcal G$, which is arbitrary.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 15, Lemma 6.1 with (12) on p. 15 (proof pp. 16–17)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_Amp
import Definitions.Def_DataDepProb_Discrete_Procedure

namespace DataDepProb.Discrete

/-- Lemma 6.1 (penalized multiplicative weights, p. 15). Let `n ≥ 1`, `η, λ > 0`, `β ≥ 0`, and
let `P_s` (`s ∈ [d]^n`) be continuously differentiable and convex on an open neighborhood of
`∆̃_d`, nonnegative on `∆̃_d`, with `P_s(e_s) = 0`, satisfying (12):
`KL(p‖q)² ≤ P_s(p) + P_s(q)` for `p, q ∈ ∆̃_d`, and `E_{S∼D^n} P_S(D̃) ≤ β²` for every
`D ∈ ∆_d`. For every query mapping `𝒢 : [d]^n → [0, 1]^[d]`, every `D ∈ ∆_d` and every
`t ≥ 0`, the recursion (8) with the penalized update `U_s` of (14) satisfies
`η ℓ_t ≤ K_t − K_{t+1} + η²/32 + λβ² + 2δ_nβ + δ_n²/λ` (15). For `τ ≥ 0`, the bound also holds
with an additional `τ` if each update returns `v ∈ ∆̃_d` with
`max_{w∈∆̃_d} ⟨log(v/q⁺) + λ∇P_s(v), v − w⟩ ≤ τ`. -/
theorem lemma_6_1 {n d : ℕ} (hn : 1 ≤ n) (η lam β : ℝ) (hη : 0 < η) (hlam : 0 < lam)
    (hβ : 0 ≤ β) (P : (Fin n → Fin d) → (Fin d → ℝ) → ℝ)
    (hPreg : ∀ s, ∃ U : Set (Fin d → ℝ), IsOpen U ∧ truncSimplex d ⊆ U ∧
      ContDiffOn ℝ 1 (P s) U ∧ ConvexOn ℝ U (P s))
    (hPnn : ∀ s, ∀ p ∈ truncSimplex d, 0 ≤ P s p)
    (hP0 : ∀ s, P s (eInit s) = 0)
    (h12kl : ∀ s, ∀ p ∈ truncSimplex d, ∀ q ∈ truncSimplex d, kl p q ^ 2 ≤ P s p + P s q)
    (h12β : ∀ D ∈ simplex d, ∑ s : Fin n → Fin d, sampleProb D s * P s (shift D) ≤ β ^ 2)
    (G : (Fin n → Fin d) → Fin d → ℝ) (hG : ∀ s x, 0 ≤ G s x ∧ G s x ≤ 1) :
    (∀ D ∈ simplex d, ∀ t : ℕ,
      η * ellt D G (exactUpdate η lam P) t ≤
        Kt D G (exactUpdate η lam P) t - Kt D G (exactUpdate η lam P) (t + 1) + η ^ 2 / 32
          + lam * β ^ 2 + 2 * deltaN n d * β + deltaN n d ^ 2 / lam) ∧
    ∀ τ : ℝ, 0 ≤ τ → ∀ U : UpdateRule n d,
      (∀ (s : Fin n → Fin d) (q f : Fin d → ℝ) (b : ℝ), q ∈ truncSimplex d →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → 0 ≤ b → b ≤ 1 → GapLE η lam τ P s q f b (U s q f b)) →
      ∀ D ∈ simplex d, ∀ t : ℕ,
        η * ellt D G U t ≤ Kt D G U t - Kt D G U (t + 1) + η ^ 2 / 32
          + lam * β ^ 2 + 2 * deltaN n d * β + deltaN n d ^ 2 / lam + τ := by sorry

end DataDepProb.Discrete
