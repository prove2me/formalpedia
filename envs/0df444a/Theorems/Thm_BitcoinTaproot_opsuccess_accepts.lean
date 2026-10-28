-- Prove2me | Theorems.Thm_BitcoinTaproot_opsuccess_accepts
-- name    : BitcoinTaproot.opsuccess_accepts
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:35:10.027663+00:00
-- url     : https://prove2.me/theorems/b41ff250-0620-48e7-9a4c-fae148c93227
-- title:
--   OP_SUCCESSx makes the script succeed
-- statement:
--   If the `OP_SUCCESSx` pre-scan of a script returns `true`, `executeTapscript` returns `true` for every context, execution data, stack and weight: the script's body is never executed (BIP342).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.opsuccess_accepts (c : TapCtx) (ed : ExecData) (stack : List Bytes) (script : Bytes) (weight : Int)
    (h : BitcoinTaproot.opSuccessScan script.length script = some true) :
    BitcoinTaproot.executeTapscript c ed stack script weight = true := by sorry
