-- Prove2me | Theorems.Thm_BitcoinScript_p2pk_correct
-- name    : BitcoinScript.p2pk_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:44:29.095993+00:00
-- url     : https://prove2.me/theorems/9ffacb9c-027a-47d0-9685-239833ffa415
-- title:
--   Pay-to-public-key is correct
-- statement:
--   For every flag setting and oracle, signature $sig$ and key $pk$ of at most $520$ bytes,
--   $$\mathrm{verifyScriptPlain}\big([\langle sig\rangle],\ \langle pk\rangle\ \mathtt{CHECKSIG}\big) = \mathtt{true} \iff \mathrm{checkSig}(sig, pk) = \mathrm{some}\ \mathtt{true}.$$
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.p2pk_correct (f : Flags) (o : Oracle) (sig pubkey : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pubkey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain f o [.push sig] (BitcoinScript.p2pkScript pubkey) = true ↔
      o.checkSig sig pubkey = some true := by sorry
