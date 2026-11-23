-- Prove2me | Theorems.Thm_CritWinSpin_p7b_5_1_waters_compiler
-- name    : CritWinSpin.p7b_5_1_waters_compiler
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:06.726259+00:00
-- url     : https://prove2.me/theorems/5495358d-8eb2-441f-a529-3130f1c30a0b
-- title:
--   Waters verification-circuit compiler and Ising-source statistics
-- statement:
--   For every polynomial-time generated bilinear family $F$, there is a Waters verification circuit on $n_0(d)=\mathrm{poly}(d)$ wires, with $n_0(d)\ge d^2$, whose honest wire records can be evaluated and decoded uniformly in polynomial time. The record preserves the message bits, allows recovery of the message and the two signature elements, and is injective in the message and signing randomness.
--
--   Replacing the NAND gates by the constant-penalty Ising gadgets gives a symmetric, zero-diagonal rational Hamiltonian of polynomial row width, with polynomial-time public Hamiltonian and message maps. Its Gibbs law $\mu_P$ and the uniform law $V_P$ on valid records satisfy
--   $$
--   \operatorname{TV}(\mu_P,V_P)\le e^{-n_0^2},\qquad
--   \operatorname{TV}(V_P^{\otimes T},\mu_P^{\otimes T})\le T e^{-n_0^2}.
--   $$
--   The message under $V_P$ is uniform, every predictor from the other records has success probability $2^{-d}$, and the collision probability among $T$ messages is at most $\binom{T}{2}2^{-d}$.
--
--   This isolates the circuit construction and Theorem 5.1(i)--(ii); the CDH reduction is a separate lemma. The record-recovery interface is needed by that reduction to turn a fresh valid record into a Waters signature.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), §5.1–§5.2, printed pp.18–20, Theorem 5.1(i)–(ii), proof pp.20–21 using RV26 Lemmas 22–23 and MMS21 Lemma 43.

import Mathlib
import Definitions.Def_CritWinSpin_SourceReduction

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

theorem p7b_5_1_waters_compiler (F : BilinearFamily) :
    ∃ circ : WatersCircuit F, SourceCircuitRecords circ ∧
      SourceGeometry F circ.toSource ∧ SourceEfficient F circ.toSource ∧
      SourceStatistics F circ.toSource := by sorry
