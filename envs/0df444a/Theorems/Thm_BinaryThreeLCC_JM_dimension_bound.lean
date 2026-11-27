-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_dimension_bound
-- name    : BinaryThreeLCC.JM.dimension_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:38.317467+00:00
-- url     : https://prove2.me/theorems/462a99ce-eda3-490a-80ac-17abb725a4dd
-- title:
--   Dimension bound under edge expansion for a lazy tuple system (Lemma 4.1, variant)
-- statement:
--   Let $\Omega$ and $\Lambda$ be finite sets, $m=|\Omega|$, $N=|\Lambda|\ge1$, and let $W$ be a vector space over $\mathbb F_2$ with labels $v:\Omega\to W$ and $w:\Lambda\to W$. A *lazy tuple system* consists of maps $\beta:\Omega\times\Lambda\times\{0,1\}\to\Lambda$ and $\tau:\Omega\times\Lambda\times\{0,1\}\to\Omega$ such that
--
--   1. (parity) $v_u+w_a+w_{\beta(u,a,o)}+v_{\tau(u,a,o)}=0$ for all $u,a,o$;
--   2. (laziness) $\beta(u,a,0)=a$ and $\tau(u,a,0)=u$;
--   3. (right regularity) for all $u,b$: $|\{(a,o):\beta(u,a,o)=b\}|=2$;
--   4. (double stochasticity) for every $u'$: $|\{(u,a):\tau(u,a,1)=u'\}|=N$;
--   5. (cut density) for some $\kappa\ge0$ and all $S\subseteq\Omega$: $|\{(u,a):u\in S,\ \tau(u,a,1)\notin S\}|\ge\kappa|S|\,|\Omega\setminus S|$.
--
--   Put $\gamma=\kappa^2m^2/(16N^2)$, assume $\gamma\le1$, and let $r\in\mathbb N$ satisfy $m(m+1)(1-\gamma)^r\le1$. Then
--
--   $$\dim\operatorname{span}\{v_u:u\in\Omega\}\ \le\ 60\bigl(r\log_2N+\log_2(m+1)\bigr).$$
--
--   This is Lemma 4.1 of the source in the form produced by its proof: the tuples $(u,a,\beta,\tau)$ are the real and fake tuples of $\mathcal T$, the walk $u\mapsto\tau(u,a,o)$ is the lazy random walk on the transition graph, and the bound comes from the $r$-chain Kikuchi graph, Claim 5.6, Lemma 5.7 and Lemma 5.3. Choosing $r\approx\gamma^{-1}\log(m(m+1))$ recovers $O\bigl(\tfrac{N^2}{\kappa^2m^2}\log m\log N\bigr)$.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Lemma 4.1, Definition 5.1, Proposition 5.5, Claim 5.6, Lemma 5.7 (printed pp. 10, 13–17)

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem dimension_bound {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]
    [Nonempty Λ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : Ω → W) (w : Λ → W) (β : Ω → Λ → Bool → Λ) (τ : Ω → Λ → Bool → Ω)
    (hpar : ∀ u a o, v u + w a + w (β u a o) + v (τ u a o) = 0)
    (hlazy : ∀ u a, β u a false = a ∧ τ u a false = u)
    (hright : ∀ u b, (Finset.univ.filter (fun p : Λ × Bool => β u p.1 p.2 = b)).card = 2)
    (hdbl : ∀ u', (Finset.univ.filter
      (fun p : Ω × Λ => τ p.1 p.2 true = u')).card = Fintype.card Λ)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ((Finset.univ.filter (fun p : Ω × Λ => p.1 ∈ S ∧ τ p.1 p.2 true ∉ S)).card : ℝ))
    (r : ℕ)
    (hγ : κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (16 * (Fintype.card Λ : ℝ) ^ 2) ≤ 1)
    (hr : (Fintype.card Ω : ℝ) * (Fintype.card Ω + 1) *
      (1 - κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (16 * (Fintype.card Λ : ℝ) ^ 2)) ^ r ≤ 1) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) : ℝ) ≤
      60 * (r * Real.logb 2 (Fintype.card Λ) + Real.logb 2 (Fintype.card Ω + 1)) := by sorry

end BinaryThreeLCC.JM
