-- Prove2me | Theorems.Thm_APSCounting893_Main_bounded_threshold_search_with_oracle
-- name    : APSCounting893.Main.bounded_threshold_search_with_oracle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:40:40.424203+00:00
-- url     : https://prove2.me/theorems/ca3de2bd-3426-40bc-87a6-622eb71e2387
-- title:
--   Uniform bounded threshold search with one oracle
-- statement:
--   Fix an oracle language $A$. There is one total binary-word function $f$ computable by a deterministic polynomial-time oracle machine such that the following holds for every word $x$ and every integer $0\le r\le |x|$. If
--
--   $$A(\langle x,\operatorname{enc}(j)\rangle)\iff j\le r\qquad(0\le j\le |x|),$$
--
--   then
--
--   $$f(x)=\operatorname{enc}(r).$$
--
--   The machine writes its answer to the physical output tape. The same machine handles every input length and threshold. This supplies the bounded search step that converts rank-threshold queries into image dimension in Lemma 6.1.
-- source:
--   Bounded search component of Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.1 and proof, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.bounded_threshold_search_with_oracle (A : Language) :
    ∃ f : Word → Word,FunctionInPWithOracle A f ∧
      ∀ (x : Word) (r : ℕ),r≤x.length →
        (∀ j : ℕ,j≤x.length → (A (pairWord x (encodeNat j)) ↔ j≤r)) → f x=encodeNat r := by sorry
