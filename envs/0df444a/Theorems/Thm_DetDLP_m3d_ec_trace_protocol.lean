-- Prove2me | Theorems.Thm_DetDLP_m3d_ec_trace_protocol
-- name    : DetDLP.m3d_ec_trace_protocol
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T01:05:36.639141+00:00
-- url     : https://prove2.me/theorems/70a546c5-ff9c-4429-9e70-0855a01fa248
-- title:
--   EC controller trace protocol
-- statement:
--   The controller realizes the small scan and, on a large instance with the specified oracle calls, a bounded trace ending at the target label of a certified outcome.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3D_ECFastDefs

set_option autoImplicit false
open DetDLP DetDLP.M3D.Fast DetDLP.M3D.Fast.ECRun DetDLP.M3D.Fast.ECQueries DetDLP.M3D.Fast.ECRun.Context DetDLP.M3D.Fast.ECRun.Assembly DetDLP.M3D.Fast.NineOracleLoop DetDLP.M3D.Fast.Stage2Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m3d_ec_trace_protocol :
    (∀ (call : ECRun.Wd → ECRun.Wd → Prop) (i o y : ECRun.Wd), i.headD true = true → DetDLP_M3D_dispatch i o = false →
     call (tag9 0 (DetDLP_M3D_orderQuery i)) o → call (tag9 1 i) y → Runs call 3 i [] y) ∧
    (∀ (c : Context) (q : w3_Query) (z : w3_Label q.M q.FB.totalCoords) (call : ECRun.Wd → ECRun.Wd → Prop)
    (U : Fin q.FB.totalCoords → q.FB.BlockTuple)
    (size : q.FB.totalCoords=c.size) (head : c.i.headD true=true) (large : DetDLP_M3D_dispatch c.i c.o=true)
    (order : call (tag9 0 (DetDLP_M3D_orderQuery c.i)) c.o)
    (plan : call (tag9 2 (curveWord c.i)) c.p) (enumerate : call (tag9 3 c.p) c.k)
    (u : ℕ → ECRun.Wd) (dec : ∀ j < c.size, call (tag9 5 (c.decQ j)) (u j))
    (gen : ∃ t, w3_update ((w3_initRows q.FB q.M U)[0]'(by simp [w3_initRows]))
        (w3_full q.M q.FB.totalCoords) t ∧ Stage2Trace.Invariant z t ∧ call (tag9 8 c.genQ) (repWord t))
    (step : ∀ j (hj : j<c.size) s, Stage2Trace.Invariant z s → ∃ t,
      w3_update ((w3_initRows q.FB q.M U)[j+1]'(by
        simpa only [w3_initRows,List.length_cons,List.length_map,List.length_finRange,Nat.succ_lt_succ_iff,size] using hj)) s t ∧
      Stage2Trace.Invariant z t ∧ call (tag9 8 (c.updQ j (repWord s) (u j))) (repWord t))
    (hm : c.blocks.length=q.m) (hmod : c.modulus=q.M) (hM : 2 ≤ q.M)
    (target : q.FB.targetCoord.val=c.blocks.flatten.length+1)
    (fixed : ∀ X Y, (q.code X Y).length=c.depth) (inj : Function.Injective (Function.uncurry q.code))
    (packets results : (w3_Rep q.M q.FB.totalCoords) → ECRun.Wd → ECRun.Wd)
    (terminal : ∀ (s : (w3_Rep q.M q.FB.totalCoords)) f, f.length ≤ c.depth →
      call (tag9 6 (c.query (repWord s) f)) (packets s f) ∧ call (tag9 7 (packets s f)) (results s f) ∧
      ∃ (C : ℕ) (net : w3_Net (request c q s f) C), packets s f=w3_packet net ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (results s f) (BTNContract net.G net.T))
    (update : ∀ (s : (w3_Rep q.M q.FB.totalCoords)), Invariant z s → ∀ X Y, q.FB.tupleVal Y=q.FB.tupleVal X+q.P →
      ¬w3_holds (w3_shiftRow q.FB q.M X Y) s.1 → ∃ t,
        w3_update (w3_shiftRow q.FB q.M X Y) s t ∧ 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s) ∧
        call (tag9 8 (c.cutQ (repWord s) (q.code X Y))) (repWord t))
    (pass : w3_pass q.FB q.M q.P z),
    ∃ y n, w3_Outcome q.FB q.M q.P U y ∧ n ≤ Nat.clog 2 (q.M^q.FB.totalCoords) ∧
      Runs call (2+n*(2*c.depth+3)+2*c.size+5) c.i [] (countWord (y q.FB.targetCoord).val)) := by sorry
