-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_lemma_38
-- name    : CompetitiveChores.RichFamily.lemma_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:39.424057+00:00
-- url     : https://prove2.me/theorems/6ff0bb34-1a93-4cb4-9375-c470aadbb77a
-- title:
--   Lemma 38 (1)–(3) — competitive ⇔ inequalities (14) ⇔ maximal welfare with weights b_i/u_i(z_i)
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$, and let $z$ be a feasible allocation. The following statements are equivalent:
--   1. $z$ is competitive.
--   2. (*characterization by inequalities*) The utility profile $u(z)$ has strictly negative components, and $z_{i,j}>0$ implies
--   $$\frac{v_{i,j}\,b_i}{u_i(z_i)}\ge\frac{v_{i',j}\,b_{i'}}{u_{i'}(z_{i'})}\qquad\text{for all } i'\in[n].\tag{14}$$
--   3. (*variational characterization*) The utility profile $u(z)$ has strictly negative components and
--   $$z\in\arg\max_{\text{feasible } y}\ \sum_{i=1}^n\frac{b_i}{u_i(z_i)}\,u_i(y_i),$$
--   i.e. $z$ has the highest weighted utilitarian welfare among all feasible allocations for the weights $\tau_i=b_i/u_i(z_i)$.
--
--   These characterizations do not involve prices; the third one says that a competitive allocation is a welfare maximizer for weights computed from its own utilities, which links the competitive rule to MWW graphs.
--
--   **Formalization Note** The paper's Lemma 38 has a fourth item (the analogue of the Eisenberg–Gale characterization: $u(z)$ is a critical point of the Nash social welfare on $\mathcal U(v)$); it is not part of this statement. "An allocation $z$" is read as a feasible allocation, since item 1 includes feasibility.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 51, Appendix A.2, Lemma 38, items 1–3, formula (14)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Lemma 38 (1)–(3), p. 51: for `v`, `b` with strictly negative entries and a feasible allocation `z`,
the following are equivalent: (1) `z` is competitive; (2) `u(z) < 0` and the inequalities (14);
(3) `u(z) < 0` and `z` maximizes the weighted utilitarian welfare with weights `τ_i = b_i / u_i(z_i)`
among all feasible allocations. Item (4) of the lemma is not part of this statement. -/
theorem lemma_38 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (hz : IsFeasible z) :
    List.TFAE
      [ IsCompetitive v b z,
        (∀ i, utilityProfile v z i < 0) ∧
          ∀ i j, 0 < z i j → ∀ i',
            v i' j * b i' / utilityProfile v z i' ≤ v i j * b i / utilityProfile v z i,
        (∀ i, utilityProfile v z i < 0) ∧
          ∀ y, IsFeasible y →
            ∑ i, b i / utilityProfile v z i * utilityProfile v y i ≤
              ∑ i, b i / utilityProfile v z i * utilityProfile v z i ] := by sorry

end CompetitiveChores.RichFamily
