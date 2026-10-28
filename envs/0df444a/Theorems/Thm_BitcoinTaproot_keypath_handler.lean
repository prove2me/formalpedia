-- Prove2me | Theorems.Thm_BitcoinTaproot_keypath_handler
-- name    : BitcoinTaproot.keypath_handler
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:36:42.766746+00:00
-- url     : https://prove2.me/theorems/b2c1f6eb-6287-409d-a227-4d28f332b91e
-- title:
--   The key path is a Schnorr check of the output key
-- statement:
--   For a single-element witness `[sig]`, the Taproot handler equals `checkSchnorrSignature` of `sig` against the 32-byte program under the key-path execution data (no annex, no tapleaf, code separator 0xFFFFFFFF).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_handler (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false ⟨false, [], [], 0xFFFFFFFF⟩ := by sorry
