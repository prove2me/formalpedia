-- Prove2me | Theorems.Thm_AvgWorstGap_np_sub_bpp_imp_ph_sub_bpp
-- name    : AvgWorstGap.np_sub_bpp_imp_ph_sub_bpp
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:55.567211+00:00
-- url     : https://prove2.me/theorems/3a9f38bc-1977-4d59-aa24-d63d5f6e14fa
-- title:
--   §3, p.19 — NP ⊆ BPP implies PH ⊆ BPP
-- statement:
--   If $\mathsf{NP}\subseteq\mathsf{BPP}$, then $\mathsf{PH}\subseteq\mathsf{BPP}$.
--
--   This is the standard collapse (it follows from $\mathsf{NP}^{\mathsf{BPP}}\subseteq\mathsf{BPP}^{\mathsf{NP}}$ by induction on the level). The paper uses it to combine Theorems 3.1 and 3.2 into Theorem 1.1, and in the proof of Lemma 3.3.
--
--   Differences from the source:
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §3, p.19 (unnumbered; also in the proof of Lemma 3.3, p.20)

import Mathlib
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **NP ⊆ BPP implies PH ⊆ BPP** (the standard fact used in arXiv:2610.19162, version of October 30, 2026, §3, p.19: "Theorem 1.1
follows directly from the following two theorems using that NP ⊆ BPP implies PH ⊆ BPP"; also in the
proof of Lemma 3.3, p.20). -/
theorem np_sub_bpp_imp_ph_sub_bpp (h : NPSubBPP) : PHSubBPP := by sorry

end AvgWorstGap
