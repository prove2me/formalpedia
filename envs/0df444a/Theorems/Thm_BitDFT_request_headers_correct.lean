-- Prove2me | Theorems.Thm_BitDFT_request_headers_correct
-- name    : BitDFT.request_headers_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:10:36.234088+00:00
-- url     : https://prove2.me/theorems/a16203a8-ef56-4060-9bd4-d66a58233147
-- title:
--   Parse both native request headers in linear time
-- statement:
--   For arbitrary binary words n, b, and r, let h(v) consist of |v| ones, a zero, and v. Starting from its ordinary native input configuration with input h(n)h(b)r, a single fixed five-tape machine halts within 2|n|+2|b|+9 transitions. Its full final configuration retains n on tape 4 and b on tape 3, clears the counter tape, leaves output empty, and places the input head at the beginning of r. Empty fields and an empty suffix are allowed.
-- source:
--   An actual native-input parser component of the integer-multiplication-to-DFT transfer. It closes the preparation assumption for the two retained header fields, but does not itself compute guard precision or the DFT.

import Definitions.Def_BitDFT_RequestHeaders
open BitDFT.RequestHeaders IntMul

theorem BitDFT.request_headers_correct (n b rest : List Bool) :
    ∃ t, t ≤ 2*n.length+2*b.length+9 ∧
      machine.step^[t] (machine.initCfg (header n++header b++rest) []) =
        final (header n++header b++rest) n b := by sorry
