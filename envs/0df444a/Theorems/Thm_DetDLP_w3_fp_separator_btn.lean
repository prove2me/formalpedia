-- Prove2me | Theorems.Thm_DetDLP_w3_fp_separator_btn
-- name    : DetDLP.w3_fp_separator_btn
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T20:54:52.364804+00:00
-- url     : https://prove2.me/theorems/71c6831b-aee7-4bf7-9678-92cf13aad050
-- title:
--   Stage II: full-group lookup-separator BTN construction
-- statement:
--   For every prime-field input, affine-interval seed and explicit factor-base blocks in the stated large-modulus regime, construct a deterministic native-address lookup-separator BTN for fixed-shift filtering. The witness must satisfy the Section 4.2 lookup/separator geometry, evaluate every address including invalid addresses uniformly in polynomial time and space, be parsimonious for precisely the valid prefix-compatible tuple pairs, have exact Newton-binomial readout over the specified truncated polynomial ring, and prove a no-wraparound integer bound for the positive-filter sum. The family includes the seed, lists, labels and prefix as the canonical public input.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Separator
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_fp_separator_btn : w3_Separator w3_fpQueries := by sorry
