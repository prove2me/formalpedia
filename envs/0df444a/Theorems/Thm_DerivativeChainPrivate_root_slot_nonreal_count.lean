-- Prove2me | Theorems.Thm_DerivativeChainPrivate_root_slot_nonreal_count
-- name    : DerivativeChainPrivate.root_slot_nonreal_count
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:49:33.177447+00:00
-- url     : https://prove2.me/theorems/4532887d-ab12-45be-b65f-89dea33926d3
-- title:
--   The proposal root-slot count matches the real-polynomial defect
-- statement:
--   If a real polynomial complexifies to the proposal product fromRoots a, its real-root defect equals nonrealCount a. Repeated original root slots are counted separately.
-- source:
--   Derivative-zero chains: public formalization reference, R30, DerivativeChainPrivate.root_slot_nonreal_count. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_nonreal_roots_of_real_polynomial

set_option autoImplicit false
open DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.root_slot_nonreal_count {n : ℕ} (a : Fin n → ℂ) (p : Polynomial ℝ)
    (hp : p.map Complex.ofRealHom = fromRoots a) :
    p.natDegree - p.roots.card = nonrealCount a := by sorry
