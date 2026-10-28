-- Prove2me | Theorems.Thm_BitcoinTaproot_minimalif_rejects
-- name    : BitcoinTaproot.minimalif_rejects
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:35:40.624755+00:00
-- url     : https://prove2.me/theorems/edb55953-d4aa-4dfb-aba2-bfb7c6b68462
-- title:
--   MINIMALIF is consensus in Tapscript
-- statement:
--   An executed `OP_IF` whose top stack element is longer than one byte, or is one byte other than `0x01`, is a script error (`SCRIPT_ERR_TAPSCRIPT_MINIMALIF`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.minimalif_rejects (c : TapCtx) (ed : ExecData) (ts : TapState) (top : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = top :: rest) (h : 1 < top.length ∨ (top.length = 1 ∧ (top.getD 0 0).toNat ≠ 1)) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_IF ts = none := by sorry
