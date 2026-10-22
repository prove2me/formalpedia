-- Prove2me | Theorems.Thm_FermiCap_Gaussian_lemma_3
-- name    : FermiCap.Gaussian.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:05.730523+00:00
-- url     : https://prove2.me/theorems/be072b71-3cce-4682-a31f-b2eea1af0f50
-- title:
--   Lemma 3 — even pure three-qubit states are even Gaussian
-- statement:
--   If $\rho$ is a pure state of three qubits and has even parity, meaning $P\rho=\rho$ for $P=Z\otimes Z\otimes Z$, then
--   $$\rho\text{ is even Gaussian.}$$
--   The paper's displayed lemma says “Gaussian”; its proof establishes the stronger even-Gaussian form used here. This low-dimensional parity result supports the two-qubit clause of Theorem 1.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 6, Lemma 3 and its proof

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States

noncomputable section

namespace FermiCap.Gaussian

/-- Lemma 3, in the stronger form established by its proof: an even pure
three-qubit state is even Gaussian. -/
theorem lemma_3 (ρ : Op 3) (hpure : IsPure ρ) (heven : IsEven ρ) :
    IsEvenGaussian ρ := by sorry

end FermiCap.Gaussian
