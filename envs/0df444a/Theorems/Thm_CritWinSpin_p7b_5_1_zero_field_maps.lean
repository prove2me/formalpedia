-- Prove2me | Theorems.Thm_CritWinSpin_p7b_5_1_zero_field_maps
-- name    : CritWinSpin.p7b_5_1_zero_field_maps
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:16.491831+00:00
-- url     : https://prove2.me/theorems/35653a35-2af8-4c90-960c-08108ecb0fde
-- title:
--   Effective Hamiltonian and message maps for the zero-field lift
-- statement:
--   Let $(H,\Omega,\Psi)$ be a binary Ising source whose public Hamiltonian encoding and message map are uniformly polynomial-time computable. For its zero-field lift
--   $$
--   \widehat H(t,z)=H(tz),\qquad \widehat\Psi(t,z)=\Psi(tz),
--   $$
--   the public-key-to-Hamiltonian encoding map and the map $(P,(t,z))\mapsto\widehat\Psi_P(t,z)$ are also uniformly polynomial-time computable.
--
--   The Hamiltonian computation implements equation (26): it moves the linear field $h_0$ to interactions with the new spin $t$, retains the old quadratic block, and sets the new external field to zero. The message computation forms $tz$ by coordinatewise sign multiplication and applies the original message map. This lemma contains only the effective encoding maps; the independent-sign adversary wrapper is separate.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), §5.2, eq. (26), printed pp.19–20; Theorem 5.1 zero-field argument, printed p.21.

import Mathlib
import Definitions.Def_CritWinSpin_SourceReduction

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

theorem p7b_5_1_zero_field_maps (F : BilinearFamily) (src : BinarySource F)
    (heff : SourceEfficient F src) :
    (∃ hamF_hat : Str → Str, CookPvsNP.PolyTimeComputable hamF_hat ∧
      ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        hamF_hat (pkCode F d desc key) = encInst ((hatSource src).ham d desc key)) ∧
    (∃ psiF_hat : Str → Str, CookPvsNP.PolyTimeComputable psiF_hat ∧
      ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (src.n d + 1)),
        psiF_hat (tupleCode [pkCode F d desc key, List.ofFn y]) =
          List.ofFn ((hatSource src).psi d desc key y)) := by sorry
