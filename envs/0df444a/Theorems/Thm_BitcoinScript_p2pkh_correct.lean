-- Prove2me | Theorems.Thm_BitcoinScript_p2pkh_correct
-- name    : BitcoinScript.p2pkh_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:44:37.939001+00:00
-- url     : https://prove2.me/theorems/bf63253f-8e11-4274-b993-ba8ceae7f5f3
-- title:
--   Pay-to-public-key-hash is correct
-- statement:
--   For every flag setting and oracle, signature $sig$, public key $pk$ and hash $h$ each of at most $520$ bytes,
--   $$\mathrm{verifyScriptPlain}\big([\langle sig\rangle, \langle pk\rangle],\ \mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}\big) = \mathtt{true} \iff \mathrm{hash160}(pk) = h \;\wedge\; \mathrm{checkSig}(sig, pk) = \mathrm{some}\ \mathtt{true}.$$
--   Here `verifyScriptPlain` evaluates the `scriptSig` and then the `scriptPubKey` on the same stack with the transcribed `EvalScript` — element-size, operation-count and stack-size checks included — and requires a true top; `hash160` and `checkSig` are the oracle's. The template that carries most of Bitcoin's history therefore enforces exactly "the key hashes to $h$ and the signature verifies", in both directions, for every oracle.
--
--   **Formalization Note.** The 520-byte bounds are the `MAX_SCRIPT_ELEMENT_SIZE` push checks; no assumption is made on the oracle, on the flags, or on the length of $h$ beyond the push limit.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.p2pkh_correct (f : Flags) (o : Oracle) (sig pubkey h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pubkey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain f o [.push sig, .push pubkey] (BitcoinScript.p2pkhScript h) = true ↔
      o.hash160 pubkey = h ∧ o.checkSig sig pubkey = some true := by sorry
