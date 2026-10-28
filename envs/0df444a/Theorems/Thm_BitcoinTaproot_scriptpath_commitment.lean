-- Prove2me | Theorems.Thm_BitcoinTaproot_scriptpath_commitment
-- name    : BitcoinTaproot.scriptpath_commitment
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:37:17.522856+00:00
-- url     : https://prove2.me/theorems/db7b650e-8a99-41d4-b505-86ea38666213
-- title:
--   A verifying script-path spend has a valid commitment
-- statement:
--   If a witness `stack ++ [script, control]` without an annex verifies under the Taproot handler, then `verifyTaprootCommitment control q leafHash = true`, where `leafHash` is the tapleaf hash of the revealed script under the control byte's masked leaf version: the merkle path from the leaf, tweaked into the internal key, yields the output key with the control byte's parity.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.scriptpath_commitment (spent : List TxOut) (c : BitcoinVerify.Ctx) (stack : List Bytes)
    (script control q : Bytes) (hna : BitcoinTaproot.hasAnnex (stack ++ [script, control]) = false)
    (h : BitcoinTaproot.taprootHandler spent c (stack ++ [script, control]) q = true) :
    BitcoinTaproot.verifyTaprootCommitment control q
      (BitcoinTaproot.tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& BitcoinTaproot.TAPROOT_LEAF_MASK)) script) = true := by sorry
