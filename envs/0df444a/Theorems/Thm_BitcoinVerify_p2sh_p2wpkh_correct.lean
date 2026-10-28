-- Prove2me | Theorems.Thm_BitcoinVerify_p2sh_p2wpkh_correct
-- name    : BitcoinVerify.p2sh_p2wpkh_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:06:40.353547+00:00
-- url     : https://prove2.me/theorems/634c5e2d-856b-4540-bcff-9c71e44dd670
-- title:
--   P2SH-wrapped P2WPKH is correct
-- statement:
--   With both flags, the output `OP_HASH160 <Hash160(OP_0 <h>)> OP_EQUAL` spent with scriptSig `<OP_0 <h>>` and witness `[sig, pk]` verifies iff $h$ is true as a script value, $\mathrm{Hash160}(pk) = h$ and the BIP143 signature check on the implied P2PKH script accepts.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2sh_p2wpkh_correct (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hp : c.flags.p2sh = true) (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c (BitcoinSig.pushBytes (BitcoinVerify.witnessBytes 0 h))
        (BitcoinVerify.p2shBytes (BitcoinSer.hash160 (BitcoinVerify.witnessBytes 0 h))) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
