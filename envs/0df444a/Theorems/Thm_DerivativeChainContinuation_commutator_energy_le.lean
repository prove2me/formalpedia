-- Prove2me | Theorems.Thm_DerivativeChainContinuation_commutator_energy_le
-- name    : DerivativeChainContinuation.commutator_energy_le
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:42:15.856174+00:00
-- url     : https://prove2.me/theorems/f3b3b648-e418-4229-982b-ff06fecb2244
-- title:
--   Commutator energy controlled by off-diagonal energy
-- statement:
--   Let $T$ be a complex square matrix. Suppose $\|Tv\|^2\le r\|v\|^2$ and $\|T^*v\|^2\le r\|v\|^2$ for every vector $v$. Then $$\|TT^*-T^*T\|_F^2\le16r\left(\|T\|_F^2-\sum_i|T_{ii}|^2\right).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CommutatorBound.lean#L8-L41

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_MatrixEnergy
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.commutator_energy_le {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (r : ℝ)
    (hT : SquareBound T r) (hTs : SquareBound T.conjTranspose r) :
    frobeniusSq (T*T.conjTranspose-T.conjTranspose*T) ≤
      16*r*(frobeniusSq T-∑ i, Complex.normSq (T i i)) := by sorry
