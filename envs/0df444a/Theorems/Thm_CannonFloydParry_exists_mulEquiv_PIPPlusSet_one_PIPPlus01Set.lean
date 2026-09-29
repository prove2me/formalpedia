-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_PIPPlusSet_one_PIPPlus01Set
-- name    : CannonFloydParry.exists_mulEquiv_PIPPlusSet_one_PIPPlus01Set
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:07:07.003613+00:00
-- url     : https://prove2.me/theorems/5350f808-d4bd-419f-8a61-2777d0b726d9
-- title:
--   p. 251 — PIP⁺(Δ₁) is isomorphic to its model on [0,1]
-- statement:
--   There are a subgroup $H$ of the homeomorphisms of $\Delta_1$ with elements exactly $PIP^+(\Delta_1)$, a subgroup $K$ of the order isomorphisms of $[0,1]$ with elements exactly the PIP⁺ maps of $[0,1]$ (`PIPPlus01Set`), and an isomorphism $\varphi \colon H \to K$ that is conjugation by $t \mapsto (t, 1-t)$: $(\varphi f)(t) = s$ exactly when $f(t, 1-t) = (s, 1-s)$.
--
--   **Formalization Note.** The source moves $\Delta_1$ to $\Delta_1' = \{(t,1)\}$ by a matrix in $SL(2,\mathbb{Z})$ and identifies $\Delta_1'$ with $[0,1]$ by $t \mapsto (t,1)$; the composite identification of $[0,1]$ with $\Delta_1$ is $t \mapsto (t, 1-t)$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 251, the simplex Δ₁′

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_mulEquiv_PIPPlusSet_one_PIPPlus01Set :
    ∃ (H : Subgroup (Simplex 1 ≃ₜ Simplex 1)) (K : Subgroup (UI ≃o UI)),
      (H : Set (Simplex 1 ≃ₜ Simplex 1)) = PIPPlusSet 1 ∧ (K : Set (UI ≃o UI)) = PIPPlus01Set ∧
      ∃ φ : H ≃* K, ∀ (f : H) (t : UI),
        toSimplexOne ((φ f : UI ≃o UI) t) = (f : Simplex 1 ≃ₜ Simplex 1) (toSimplexOne t) := by
  sorry

end CannonFloydParry
