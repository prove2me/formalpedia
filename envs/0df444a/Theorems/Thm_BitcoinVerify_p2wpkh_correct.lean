-- Prove2me | Theorems.Thm_BitcoinVerify_p2wpkh_correct
-- name    : BitcoinVerify.p2wpkh_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:06:50.806551+00:00
-- url     : https://prove2.me/theorems/b5e06a47-1342-4880-85c7-323ce687e618
-- title:
--   Native P2WPKH is correct
-- statement:
--   With the `WITNESS` flag, for a 20-byte $h$ and signature and key within 520 bytes:
--   $$\mathrm{verifyScript}\big([\,],\ \mathtt{OP\_0}\ \langle h\rangle,\ [sig, pk]\big) = \mathtt{true} \iff \mathrm{castToBool}(h) \wedge \mathrm{Hash160}(pk) = h \wedge \mathrm{checkSigPreTapscript}_{\mathrm{WITNESS\_V0}}(\text{p2pkhBytes}(h), sig, pk) = \mathrm{some}\ \mathtt{true},$$
--   where the signature check is the signature mission's checker under witness v0 (BIP143 sighash, `DERSIG` from the flags) on the implied script `DUP HASH160 <h> EQUALVERIFY CHECKSIG`. The first conjunct records that an all-zero key hash is unspendable: the base evaluation of `OP_0 <h>` leaves $h$ on top and requires it true.
--
--   **Formalization Note.** `verifyScript` is the full `VerifyScript` control flow with the consensus flags; the equivalence holds for every flag set with `WITNESS` on, every transaction and amount, and every Taproot handler.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2wpkh_correct (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 h) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
