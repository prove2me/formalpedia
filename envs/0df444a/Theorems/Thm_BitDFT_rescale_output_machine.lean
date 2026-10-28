-- Prove2me | Theorems.Thm_BitDFT_rescale_output_machine
-- name    : BitDFT.rescale_output_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:22:30.028649+00:00
-- url     : https://prove2.me/theorems/342a7489-388f-42ff-bbb8-d7038108d95c
-- title:
--   A machine wrapper for header conversion and exact vector scaling
-- statement:
--   Fix a correct integer multiplication machine $M$ with pointwise runtime bound $T$, an arbitrary machine $A$, and a positive constant $C$. There is a single wrapper machine $B$ and a positive constant $D$ with the following property. For $n,b\ge1$, put $q=b+3\ell(n)+5$. Whenever disc-valued precision-$q$ vectors $U,W$ satisfy that $A$ transforms the input header $(n,q)$ and vector $U$ into $W$ within $C F_T(n,q)$ steps, the wrapper transforms the header $(n,b)$ and the same $U$ into the exact integer-scaled vector $nW$ within $D F_T(n,q)$ steps, where
--   $$F_T(n,q)=T(nq)+nT(q)+q\ell(q)^2+nq.$$
--   Output magnitude fields have width $q+\ell(n)+1$. The conclusion concerns actual steps and complete output tapes in the multitape model. No Fourier accuracy assumption occurs in this wrapper statement.
-- source:
--   Original machine-interface lemma for this mission; fixed-size multiplication strategy from Harvey–van der Hoeven 2025, Lemma 3.2, https://arxiv.org/html/2503.22848v1#S3.SS4. Header conversion and output scaling are additional explicit construction obligations.
--
--   Verified input-parsing components (2026-10-24): BitDFT.header_reader_correct, https://prove2.me/theorems/c527fd43-000a-4663-afc8-f8a5c254188c (exact full run); BitDFT.header_reader_ready, https://prove2.me/theorems/cf195e45-6315-41e5-ae84-fa654fa5e1c9 (configuration-level handoff before scanning the remainder); BitDFT.requested_header_reader_bound, https://prove2.me/theorems/d38db03e-afb2-448e-bb13-2385952acfb7 (actual request encoding, at most 16*n*q transitions). These are proved components for the implementation, not a completed decomposition or proof of this rescaling theorem. Remaining construction: precision-header rewriting, composition with arbitrary A, and exact multiplier-backed output scaling/serialization.
--
--   A verified controller-composition component is now available: BitDFT.machine_sequence_bound, https://prove2.me/theorems/4883f155-228c-454f-a372-2cfe442c651e (accepted proof https://prove2.me/submissions/6788a4f1-5399-4b34-ba44-03190930f57a). Compatible finite controllers compose in at most t+1+u transitions while preserving the exact tape contents and head positions at handoff. This component requires a shared alphabet and tape layout; the wrapper still needs concrete stages, alphabet/bank adapters, header arithmetic, and output scaling. It is not a completed proof or decomposition of this theorem.
--
--   The header reader now has a verified composable stopping stage: https://prove2.me/theorems/ac6acb94-e476-407e-8af2-c6a4e48e6785 (accepted proof https://prove2.me/submissions/bf38b8bf-bec9-481c-9cfe-12bd47766034). It freezes at the internal boundary after 2k+3 steps, preserving the full parser handoff configuration without copying the remaining vector. The precision rewrite, output-scaling stages, and their complete assembly remain unproved.
--
--   Verified workspace extension: https://prove2.me/theorems/574a2a6a-9bbf-4ba3-9709-71f17e6ea2a0 (proof https://prove2.me/submissions/50906bdf-1973-4ef5-9846-6f03b2c08761). Any fixed number of extra tapes can retain arbitrary caller data while the old machine runs at exactly the same clock; ordinary binary-input halting and output are preserved. This adapter still needs to be instantiated in the concrete rescaling construction.
--
--   Verified precision-arithmetic routine: BitDFT.binary_counter_add, https://prove2.me/theorems/704c4f07-84ff-4415-9649-6f681848f0ff (accepted proof https://prove2.me/submissions/c22eb590-d8e2-4375-92e3-7e9583d2a717). The fixed four-tape machine adds a unary count K to a little-endian binary word w in at most 5K+2|w|+1 actual transitions, clears the unary tape and preserves parked native input/output data. With prepared K=3 lg(n)+5 and reversed precision bits, this implements the guard-precision arithmetic. Constructing K, reversing/serializing the header bits, and complete wrapper assembly remain separate obligations.
--
--   Verified logarithmic increment preparation: BitDFT.log_scanner_correct, https://prove2.me/theorems/9ecd9597-1ef3-488d-9b05-ef6eba2ba9ec (proof https://prove2.me/submissions/9b4969b7-ba68-4244-8faf-db6c1dba1f2e). From a canonical dimension word on its work tape, a fixed finite scanner produces K=3 lg(n)+5 unary marks in exactly K+3 transitions, preserving the dimension and parked caller data and leaving the unary head on the last mark. The scanner handles n=1 and powers of two. This supplies the count formerly assumed prepared by the binary-counter specialization; their complete composition and the rest of the wrapper still require proof.
--
--   Verified combined precision-computation program: https://prove2.me/theorems/f79da9c6-12c0-43a0-bd30-5f4d2ec309d6 (accepted proof https://prove2.me/submissions/9a1b16c0-d8a2-4192-9be8-d347c5fb74e7). One fixed five-tape machine, given a canonical dimension word and reversed requested-precision bits in its prepared work layout, constructs its own logarithmic unary count and computes q=b+3 lg(n)+5 within 7q actual transitions. Its output word has at most q bits; the exact final configuration retains the dimension and caller data and clears the unary workspace. The proof composes the scanner and bounded-output counter through the accepted tape adapters and finite sequencing theorem. Installing the initial words from the request, serializing q, calling A, and scaling outputs remain unproved parts of this wrapper.
--
--   Latest verified construction progress (2026-10-24): BitDFT.encoded_precision_correct, https://prove2.me/theorems/b6fc588b-9e05-49d4-9dca-2609ce389463 (accepted proof https://prove2.me/submissions/49870642-bcb6-459a-b486-dfdf123fd3e5); BitDFT.serialize_field_correct, https://prove2.me/theorems/a96b6719-f57d-4de0-bd32-9517ee62217d (accepted proof https://prove2.me/submissions/d1dbc663-d495-4657-ac0a-7ff20fbeb026). The native-input precision machine now starts from the actual encNat(n) encNat(b) suffix encoding and computes q within 11q transitions, with a positive little-endian output word of length at most q and a full final-configuration contract. This discharges the earlier prepared-header and prepared-count assumptions for that stage. The field serializer appends an exact self-delimiting header in 2|v|+3 transitions with caller tapes preserved. Canonicalization and assembly of the full rewritten request, arbitrary-A simulation, and multiplier-based output scaling remain obligations; this theorem is still Open, and these supporting results are not a completed decomposition of it.

import Definitions.Def_BitDFT_Numerics
set_option autoImplicit false
noncomputable section
open BitDFT

theorem BitDFT.rescale_output_machine
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (A : IntMul.MultitapeTM) (C : ℝ) (hC : 0 < C) :
    ∃ B : IntMul.MultitapeTM, ∃ D : ℝ, 0 < D ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b →
        ∀ U W : Fin n → ℤ × ℤ,
          vectorDisc (guardPrecision n b) U →
          vectorDisc (guardPrecision n b) W →
          Computes A (fourierInput (guardPrecision n b) U)
            (encVector (guardPrecision n b + 1) W)
            (C * transferCost T n (guardPrecision n b)) →
          Computes B (requestedInput b U)
            (encVector (guardPrecision n b + IntMul.lg n + 1)
              (fun k => ((n : ℤ) * (W k).1, (n : ℤ) * (W k).2)))
            (D * transferCost T n (guardPrecision n b)) := by sorry
