-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_mod_pow_two
-- name    : CollatzEndpointTransport.Terras.oddCount_mod_pow_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:40.401121+00:00
-- url     : https://prove2.me/theorems/49c26b91-4c2f-4b04-b844-3ae2bb6fb5a1
-- title:
--   Terras: odd Count mod pow two
-- statement:
--   The first `H` parity bits, and hence their odd count, are unchanged when
--   the starting value is reduced modulo `2^H`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L197-L202
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L197-L202

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.oddCount_mod_pow_two (H n : ℕ) :
    oddCount H (n % (2 ^ H)) = oddCount H n := by sorry
