-- Prove2me | Theorems.Thm_DetANN_HPIM_PP_node_spec
-- name    : DetANN.HPIM.PP.node_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T09:27:16.62628+00:00
-- url     : https://prove2.me/theorems/0f4e5769-cb90-493e-8b79-4c2302592384
-- title:
--   The node contract
-- statement:
--   Let $B$ be blocks with `Blocks.WF` and `ChildOK B`, $m\ge1$, $Y$ injective and $\delta\in(0,1/2)$. If the constants $K_W,K_H,K_R,W_I,W_R$ satisfy `Budgets` (definition `DetANN_HPIMPreProg`), then the node contract `NodeOK` holds at every fuel $f$.
--
--   In words: from NODE with a well-formed record for a set $S$ of at most $f+1$ points, the run reaches RETURN with the global invariant intact, and:
--   - it stores $\mathrm{hpimNode}(Y,\delta,f,S)$ at the record;
--   - it uses at most $\mathrm{treePts}(f,S)\cdot K_W$ work and $\mathrm{treePts}(f,S)\cdot K_H$, $\mathrm{treePts}(f,S)\cdot K_R$ heap cells;
--   - it writes only its record, the new heap and bounded scratch windows.
--
--   The proof is by induction on $f$, combining the node head (median, ladder), `lk_loop` and `kids_loop`, and a tail call on the representatives.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the intermediate steps of the reduction of DetANN.HPIM.hpim_preprocessing, split so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- **The node contract at every fuel.** -/
theorem node_spec (B : Blocks) (hB : B.WF) (ch : ChildOK B) (hm : 1 ≤ m)
    (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (KW KH KR WbI WbR : ℕ)
    (bu : Budgets Y δ T0 B ch KW KH KR WbI WbR) :
    ∀ f, NodeOK Y δ T0 v0 B KW KH KR WbI WbR f := by sorry

end DetANN.HPIM.PP
