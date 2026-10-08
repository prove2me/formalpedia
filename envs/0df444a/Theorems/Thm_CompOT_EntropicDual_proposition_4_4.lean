-- Prove2me | Theorems.Thm_CompOT_EntropicDual_proposition_4_4
-- name    : CompOT.EntropicDual.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:46.901321+00:00
-- url     : https://prove2.me/theorems/8eac4799-d0ff-4628-b0af-0b0b4db28d52
-- title:
--   Proposition 4.4 — attained entropic duality and optimal scalings
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ have strictly positive entries, let $C\in\mathbb R^{n\times m}$, and let $\varepsilon>0$. There is an optimal coupling $P$ for the entropic primal problem and a dual pair $(f,g)$ attaining the maximum
--
--   $$
--   L_C^\varepsilon(a,b)=\langle C,P\rangle-\varepsilon H(P)
--   =\max_{f',g'}\left\{\langle f',a\rangle+\langle g',b\rangle-\varepsilon\sum_{i,j}e^{f'_i/\varepsilon}K_{ij}e^{g'_j/\varepsilon}\right\}.
--   $$
--
--   Every maximizing pair $(f',g')$ gives the scaling of this primal coupling:
--
--   $$
--   P_{ij}=e^{f'_i/\varepsilon}K_{ij}e^{g'_j/\varepsilon}.
--   $$
--
--   The result connects the regularized transport minimum to a smooth unconstrained maximization and identifies the dual variables with the scaling factors.
--
--   **Formalization Note** The strictly positive marginal entries are necessary for the displayed maximum to be attained by finite real potentials; a zero marginal can force a potential to tend to $-\infty$. Indices use `Fin n` and `Fin m`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 4.4, (4.30)–(4.31), p. 448. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

namespace CompOT.EntropicDual

/-- Proposition 4.4, p. 448: strong entropic duality, attainment, and the
primal-dual scaling relation (4.31). -/
theorem proposition_4_4 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      ∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ,
        dualObjEnt C a b ε f g = entropicObj C P ε ∧
        (∀ f' g', dualObjEnt C a b ε f' g' ≤ dualObjEnt C a b ε f g) ∧
        (∀ f' g', dualObjEnt C a b ε f' g' = dualObjEnt C a b ε f g →
          ∀ i j, P i j = Real.exp (f' i / ε) * gibbs C ε i j *
            Real.exp (g' j / ε)) := by sorry

end CompOT.EntropicDual
