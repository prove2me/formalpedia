-- Prove2me | Theorems.Thm_Components_Close_Implies_Function_Close
-- name    : Components_Close_Implies_Function_Close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:30:57.206822+00:00
-- url     : https://prove2.me/theorems/d54103a2-548d-46c3-9db2-f4dff53c1cd8
-- title:
--   Components Close Implies Function Close: Components Close Implies Function Close
-- statement:
--   The Components Close Implies Function Close construction uses the Components Close Implies Function Close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L225-L253
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L225-L253

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem Components_Close_Implies_Function_Close
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (f_i : Fin m → (pow_domain D m → F))
    (h_fi_def : ∀ i, ∀ z : pow_domain D m, f_i i z = folding_component D m f i (z : F))
    (h_close : ∀ i : Fin m, ∃ u_i ∈ reedSolomon (pow_domain D m) (d / m),
      ∀ z : pow_domain S m,
        u_i ⟨z.val, pow_domain_subset hS z.2⟩ = f_i i ⟨z.val, pow_domain_subset hS z.2⟩) :
    ∃ u ∈ reedSolomon D d, ∀ x : S, u ⟨x.val, hS x.2⟩ = f x := by sorry
