-- Prove2me | Theorems.Thm_CritWinSpin_p7b_5_1_zero_field_wrapper
-- name    : CritWinSpin.p7b_5_1_zero_field_wrapper
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:58.47012+00:00
-- url     : https://prove2.me/theorems/f93f32a2-2c46-40d2-a0fe-d8d9437212e0
-- title:
--   Independent-sign PPT wrapper for zero-field forging
-- statement:
--   For every PPT algorithm $A$ attacking the zero-field source and every efficiently computable polynomial $T(d)\ge1$, there is a PPT algorithm $B$ attacking the original source with the following pointwise guarantee. Fix a public key and original training records $F_1,\dots,F_T$. Draw independent uniform signs $t_1,\dots,t_T$, replace each training record by $(t_i,t_iF_i)$, run $A$, and decode an output $(t,z)$ to $tz$. Then $B$ outputs a valid record with a fresh message with probability at least
--   $$
--   2^{-T}\sum_{t\in\{\pm1\}^T}
--   \Pr\!\left[A(P,(t_i,t_iF_i)_{i=1}^T)\in\widehat\Omega_P
--   \text{ and has fresh message}\right].
--   $$
--   Freshness is preserved because $\widehat\Psi(t,z)=\Psi(tz)$. The statement is pointwise in the key and training records, so it can subsequently be averaged over key generation and $V_P^{\otimes T}$ without any loss.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), Theorem 5.1 zero-field proof, printed p.21: drawing an independent sign and decoding a valid zero-field output preserves properties (i)–(iii).

import Mathlib
import Definitions.Def_CritWinSpin_SourceReduction

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

theorem p7b_5_1_zero_field_wrapper (F : BilinearFamily) (src : BinarySource F)
    (A : PPT) (T : ℕ → ℕ) (hT : EffPoly T) (hTpos : ∀ d, 1 ≤ T d) :
    ∃ B_wrap : PPT, ∀ (d : ℕ) (desc : Str) (key : WatersKey F desc d)
      (Fs : Fin (T d) → BinCfg (src.n d)),
      (1 / (2 : ℝ) ^ (T d)) * ∑ ts : Fin (T d) → Bool,
        A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
            List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
          (fun s => ∃ y_hat : BinCfg (src.n d + 1), s = List.ofFn y_hat ∧
            hatProd y_hat ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key (hatProd y_hat) ≠ src.psi d desc key (Fs t)) ≤
      B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
          ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t)) := by sorry
