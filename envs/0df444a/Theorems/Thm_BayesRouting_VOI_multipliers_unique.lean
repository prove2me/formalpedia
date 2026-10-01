-- Prove2me | Theorems.Thm_BayesRouting_VOI_multipliers_unique
-- name    : BayesRouting.VOI.multipliers_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:58:53.576762+00:00
-- url     : https://prove2.me/theorems/6222b0cd-9223-4acb-be92-a12855408010
-- title:
--   Lemma 3 — the Lagrange multipliers of (OPT-$\mathcal Q$) are unique and given by (13a)–(13b)
-- statement:
--   Let $q^*$ be a BWE of $\Gamma(\lambda)$, $\lambda$ in the simplex. Call $(\mu,\nu)=(\mu^{t^i},\nu^{t^i}_r)$ **KKT multipliers** at $q^*$ for the Lagrangian
--
--   $$\mathcal L(q,\mu,\nu,\lambda)=\Phi(q)+\sum_{i}\sum_{t^i}\mu^{t^i}\Big(\lambda^iD-\sum_r q^i_r(t^i)\Big)-\sum_r\sum_i\sum_{t^i}\nu^{t^i}_rq^i_r(t^i)$$
--
--   if $\partial\Phi(q^*)/\partial q^i_r(t^i)=\mu^{t^i}+\nu^{t^i}_r$, $\nu^{t^i}_r\ge0$ and $\nu^{t^i}_r\,q^{i*}_r(t^i)=0$ for all $i,t^i,r$. Define
--
--   $$\mu^{t^i*}=\min_{r\in\mathcal R}\Pr(t^i)\,\mathbb E[c_r(q^*)\mid t^i],\qquad \nu^{t^i*}_r=\Pr(t^i)\,\mathbb E[c_r(q^*)\mid t^i]-\mu^{t^i*}.$$
--
--   Then $(\mu^*,\nu^*)$ are KKT multipliers at $q^*$, and every pair of KKT multipliers coincides with $(\mu^*,\nu^*)$ on every population $i$ with $\lambda^i>0$.
--
--   These multipliers are the equilibrium costs weighted by the type probabilities; their uniqueness is what makes the optimal value $\Psi$ directionally differentiable with the derivative of Lemma 5.
--
--   **Formalization Note** The page states uniqueness for all populations. For a population with $\lambda^i=0$ it fails: then $q^{i*}=0$ and any $\mu^{t^i}\le\mu^{t^i*}$ with $\nu$ adjusted is a KKT pair. The statement is therefore restricted to populations of positive size, and this correction is disclosed. The stationarity condition uses the partial derivative of $\Phi$ as a `HasDerivAt` in the single coordinate $q^i_r(t^i)$.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Lemma 3 and Lagrangian (12)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential

open Finset

namespace BayesRouting.VOI

/-- **Lemma 3** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 154), with the KKT conditions of
(OPT-𝒬) for the Lagrangian (12) written out. Let `q` be a BWE of `Γ(λ)`. Call `(μ, ν)` KKT
multipliers at `q` if `∂Φ/∂q^i_r(t^i) = μ^{t^i} + ν^{t^i}_r`, `ν ≥ 0` and
`ν^{t^i}_r q^i_r(t^i) = 0`. Then (13a)–(13b), `μ^{t^i*} = min_r Pr(t^i) 𝔼[c_r(q) | t^i]` and
`ν^{t^i*}_r = Pr(t^i) 𝔼[c_r(q) | t^i] - μ^{t^i*}`, are KKT multipliers, and every KKT pair
coincides with them on each population of positive size. The restriction `λ^i > 0` corrects the
page: for `λ^i = 0` the multiplier `μ^{t^i}` may be any number `≤ μ^{t^i*}`. -/
theorem multipliers_unique {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (q : (i : I) → T i → R → ℝ) (hq : IsBWE G lam q) :
    let μstar : (i : I) → T i → ℝ := fun i ti =>
      univ.inf' univ_nonempty (fun r => typeProb G i ti * expCost G q i ti r)
    let νstar : (i : I) → T i → R → ℝ := fun i ti r =>
      typeProb G i ti * expCost G q i ti r - μstar i ti
    let IsKKT : ((i : I) → T i → ℝ) → ((i : I) → T i → R → ℝ) → Prop := fun μ ν =>
      (∀ i ti r, HasDerivAt (fun x => potential G (setCoord q i ti r x))
          (μ i ti + ν i ti r) (q i ti r)) ∧
        (∀ i ti r, 0 ≤ ν i ti r) ∧ (∀ i ti r, ν i ti r * q i ti r = 0)
    IsKKT μstar νstar ∧
      ∀ μ ν, IsKKT μ ν → ∀ i, 0 < lam i → ∀ ti,
        μ i ti = μstar i ti ∧ ∀ r, ν i ti r = νstar i ti r := by sorry

end BayesRouting.VOI
