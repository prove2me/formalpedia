-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_16
-- name    : DIObliviousTransfer.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:10:33.198866+00:00
-- url     : https://prove2.me/theorems/3fe1d53f-d07a-4265-91b5-a426642e2a9e
-- title:
--   Lemma 16 — post-quantum zero knowledge for NP
-- statement:
--   Assume a quantum-secure one-way function exists. Then there is a proof system that gives every NP relation a classical-message sequential proof with:
--   1. perfect completeness;
--   2. negligible statistical soundness;
--   3. quantum-computational zero knowledge: for every nonuniform QPT verifier, one QPT simulator, fixed from the verifier independently of its auxiliary state, indistinguishable uniformly on quantum auxiliary inputs entangled with a reference;
--   4. preservation of zero knowledge under polynomially many sequential invocations.
--
--   Differences from the source:
--
--   - reading: nonuniform QPT adversaries, devices and simulators with polynomial-size quantum advice → families of machines whose activations are circuits of at most two-qubit unitaries and single-wire resets with classical input loaded and output measured, all sizes bounded by one polynomial in λ; advice is part of the arbitrary initial state; reason: Decision D3 (pp.2, 17): one standard reading of nonuniform QPT
--   - reading: Real ≈c Ideal, the negligible advantage bound uniform over admissible η and fixed honest inputs → for every polynomially bounded reference size and every QPT test there is one negligible ε with advantage at most ε(λ) for every λ, every admissible η and every valid honest input; reason: Decision D4 (Definition 5 (ii)); the stronger, uniform reading
--   - encoding: every NP relation has a proof → ∃ one proof-system family ZK with ZKSpec ZK (a protocol for every NP relation); reason: the paper's construction (GMW on Naor) is one family
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 16, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_DIObliviousTransfer_ZKSpec

namespace DIObliviousTransfer

/-- **Lemma 16 (Post-quantum zero knowledge for NP)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.42 (PDF p.44). Under qOWFs, every NP relation
has a classical-message sequential proof with perfect completeness, negligible statistical
soundness, and quantum-computational zero knowledge: for every nonuniform QPT verifier one QPT
simulator, fixed from the verifier independently of its auxiliary state, whose output is
computationally indistinguishable from the real verifier's uniformly on quantum auxiliary inputs
entangled with an inaccessible reference; polynomially many sequential invocations preserve this.

**Formalization Note** (decisions D3, D4, D14). "Under qOWFs" is the existence of a quantum-secure
one-way function (`QOWF`, against nonuniform QPT inverters with quantum advice); the proof system
is one family of protocols, one per NP relation, and its properties are `ZKSpec`. -/
theorem lemma_16 (hOWF : ∃ f : Bits → Bits, QOWF f) :
    ∃ ZK : (Bits → Bits → Bool) → (ℕ → ℕ) → Protocol, ZKSpec ZK := by sorry

end DIObliviousTransfer
