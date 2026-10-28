-- Prove2me | Theorems.Thm_BitcoinTaproot_checkmultisig_rejected
-- name    : BitcoinTaproot.checkmultisig_rejected
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:35:29.184989+00:00
-- url     : https://prove2.me/theorems/c94aa26f-2757-4b48-958f-9ec95bd48ac3
-- title:
--   OP_CHECKMULTISIG is disabled in Tapscript
-- statement:
--   For every context, execution data, execution flag and state, `tapExecOp` on `OP_CHECKMULTISIG` and on `OP_CHECKMULTISIGVERIFY` is `none` (`SCRIPT_ERR_TAPSCRIPT_CHECKMULTISIG`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.checkmultisig_rejected (c : TapCtx) (ed : ExecData) (fExec : Bool) (ts : TapState) :
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIG ts = none ∧
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIGVERIFY ts = none := by sorry
