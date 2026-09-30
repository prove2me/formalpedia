-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_lemma32_kappa_perturbation
-- name    : ChitourPrescribedTime.FixedTime.lemma32_kappa_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:08:55.164976+00:00
-- url     : https://prove2.me/theorems/c51298db-174d-4d58-b999-3fce37d4437c
-- title:
--   Lemma 32 — $|\omega^H_\kappa-\omega^H_0|$ and $|V_\kappa-V_0|$ are $O(|\kappa|^{\min(1,r_n)})$ on $B^\kappa_{1-m,1+m}$
-- statement:
--   Let $n\ge1$, gains $\ell_1,\dots,\ell_n>0$ and $m\in(0,1)$. There are constants $C^1_n,C^2_n>0$, depending only on $m$ and the gains, such that for every $\kappa\in[-\tfrac1{2n},\tfrac1{2n}]$ and every $x\in B^\kappa_{1-m,1+m}$,
--   $$|\omega^H_\kappa(x)-\omega^H_0(x)|\le C^1_n|\kappa|^{\min(1,r_n)},\qquad |V_\kappa(x)-V_0(x)|\le C^2_n|\kappa|^{\min(1,r_n)},$$
--   where $r_n=r_n(\kappa)=1+(n-1)\kappa$.
--
--   These estimates quantify how far the degree-$\kappa$ controller and Lyapunov function are from the linear ones, which is what fixes an admissible $\kappa_0$ in Proposition 33.
--
--   **Formalization Note** The page writes each estimate as a maximum over $\kappa$ and $x$ bounded by an expression in $\kappa$; the only coherent reading, used here, is pointwise in $(\kappa,x)$. The constants are "explicit" on the page; the statement asserts existence, with the constants quantified before $\kappa$ and $x$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1039, Lemma 32, eqs. (56)–(57)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov

namespace ChitourPrescribedTime.FixedTime

/-- Lemma 32 (p. 1039), read pointwise: there are constants `C¹_n, C²_n > 0` (depending on `m`
and the gains) such that for every `κ ∈ [-1/(2n), 1/(2n)]` and every `x ∈ B^κ_{1-m,1+m}`,
`|ω^H_κ(x) - ω^H_0(x)| ≤ C¹_n |κ|^{min(1, r_n)}` and `|V_κ(x) - V_0(x)| ≤ C²_n |κ|^{min(1, r_n)}`,
with `r_n = r_n(κ) = 1 + (n - 1)κ`. -/
theorem lemma32_kappa_perturbation (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin n → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (m : ℝ) (hm : m ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∃ C2 : ℝ, 0 < C2 ∧
      ∀ κ ∈ Set.Icc (-(1 / (2 * (n : ℝ)))) (1 / (2 * (n : ℝ))),
        ∀ x : EuclideanSpace ℝ (Fin n), 1 - m ≤ lyapV ℓ κ x → lyapV ℓ κ x ≤ 1 + m →
          |omegaH ℓ κ x - omegaH ℓ 0 x| ≤ C1 * |κ| ^ min 1 (weight κ n) ∧
          |lyapV ℓ κ x - lyapV ℓ 0 x| ≤ C2 * |κ| ^ min 1 (weight κ n) := by sorry

end ChitourPrescribedTime.FixedTime
