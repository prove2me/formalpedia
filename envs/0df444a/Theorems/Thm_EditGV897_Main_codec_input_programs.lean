-- Prove2me | Theorems.Thm_EditGV897_Main_codec_input_programs
-- name    : EditGV897.Main.codec_input_programs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:34:58.003218+00:00
-- url     : https://prove2.me/theorems/75a5def5-1075-42e7-8418-a1fb8b600e4d
-- title:
--   Uniform codec programs polynomial in encoded input length
-- statement:
--   For every fixed edit budget $t$, there are fixed finite binary tape programs computing the specified encoder and decoder from their dimension, shared parameters and framed-word inputs. The encoder is correct on every information message. The decoder computes the specified default empty output when its definition returns no result. Their actual halting executions are bounded, respectively, by
--
--   $$A_e(\ell+1)^{d_e},\qquad A_d(\ell+1)^{d_d},$$
--
--   where $\ell$ is the corresponding encoded input length and both coefficients are positive. The programs and bounds are fixed before the block length and input. Together with the constructor's polynomial output-size bound, this gives the uniform polynomial-in-block-length execution bounds in Theorem 1.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Theorem 1 and §4 main proof, printed pp.5,13 / PDF pp.6,14. Operational implementation interface for the specified setup and codec algorithms.

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.codec_input_programs (t : ℕ) :
    ∃ (encoder decoder : Program) (Ae de Ad dd : ℕ), 0 < Ae ∧ 0 < Ad ∧
      ∀ (n : ℕ) (P : Parameters n),
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord (canonicalFamily t n) P u))
            (polyBudget Ae de (editEncoderInput P u).length)) ∧
        (∀ y : List Bit,
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget Ad dd (editDecoderInput P y).length)) := by sorry
