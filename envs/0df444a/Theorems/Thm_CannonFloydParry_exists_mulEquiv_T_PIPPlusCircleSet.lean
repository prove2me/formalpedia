-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_T_PIPPlusCircleSet
-- name    : CannonFloydParry.exists_mulEquiv_T_PIPPlusCircleSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:11:05.19942+00:00
-- url     : https://prove2.me/theorems/d8bc158d-b8f3-417d-bcfa-e29d82020f68
-- title:
--   Theorem 7.3 — T ≅ PIP⁺(S¹), with A, B, C going to the maps of p. 254
-- statement:
--   The orientation-preserving PIP homeomorphisms of the circle form a subgroup $H$ of the permutations of $S^1 = \mathbb{R}/\mathbb{Z}$, and there is an isomorphism $\varphi \colon T \to H$ that sends $T$'s generators $A$, $B$, $C$ to the three maps of p. 254: $\varphi(A)[t] = [A(t)]$, $\varphi(B)[t] = [B(t)]$, $\varphi(C)[t] = [C(t)]$ for $t \in [0,1]$, where
--   $$A(t) = \tfrac{t}{t+1},\ \tfrac{-t+1}{-5t+4},\ \tfrac{2t-1}{t} \text{ on } [0,\tfrac12], [\tfrac12,\tfrac23], [\tfrac23,1],$$
--   $$B(t) = t,\ \tfrac{3t-1}{4t-1},\ \tfrac{-6t+5}{-11t+9},\ \tfrac{2t-1}{t} \text{ on } [0,\tfrac12], [\tfrac12,\tfrac23], [\tfrac23,\tfrac34], [\tfrac34,1],$$
--   $$C(t) = \tfrac{-3t+2}{-5t+3},\ \tfrac{2t-1}{t},\ \tfrac{5t-3}{7t-4} \text{ on } [0,\tfrac12], [\tfrac12,\tfrac23], [\tfrac23,1].$$
--   The statement includes that $A$, $B$, $C$ lie in $T$.
--
--   **Formalization Note.** Theorem 7.3 says only $T \cong PIP^+(S^1)$; the sentence after it names the maps corresponding to $A$, $B$, $C$, and the goal includes them, so the isomorphism is the one the source means. They are exactly the conjugates of $T$'s $A$, $B$, $C$ by Minkowski's question mark function.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 254, Theorem 7.3

import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_mulEquiv_T_PIPPlusCircleSet :
    ∃ H : Subgroup (Equiv.Perm UnitAddCircle),
      (H : Set (Equiv.Perm UnitAddCircle)) = PIPPlusCircleSet ∧
      ∃ φ : T ≃* H,
        (∃ g : T, (g : Equiv.Perm UnitAddCircle) = symT FormalABC.A ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (φ g : Equiv.Perm UnitAddCircle) (t : UnitAddCircle) = ((pipA t : ℝ) : UnitAddCircle)) ∧
        (∃ g : T, (g : Equiv.Perm UnitAddCircle) = symT FormalABC.B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (φ g : Equiv.Perm UnitAddCircle) (t : UnitAddCircle) = ((pipB t : ℝ) : UnitAddCircle)) ∧
        (∃ g : T, (g : Equiv.Perm UnitAddCircle) = symT FormalABC.C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (φ g : Equiv.Perm UnitAddCircle) (t : UnitAddCircle) = ((pipC t : ℝ) : UnitAddCircle)) := by
  sorry

end CannonFloydParry
