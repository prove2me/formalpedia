-- Prove2me | Theorems.Thm_DQIShattered_usd_decoder
-- name    : DQIShattered.usd_decoder
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:12.442569+00:00
-- url     : https://prove2.me/theorems/64ab83e8-e8ac-4369-b9f0-ec988af9000c
-- title:
--   §3.2, pp.14, 16 — the USD decoder succeeds exactly when $B_S$ has full row rank
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$ and $\gamma\in[0,1/2]$. There is a measurement of the $M$ received qubits whose outcome is either a codeword estimate or "fail", with the following property for every $d\in C^\perp$, on input $|\psi_{d,\gamma}\rangle$.
--
--   1. It outputs $d$ with probability exactly
--   $$\mathbb P_S\big[B_S\text{ has full row rank}\big].$$
--   Here $S\subseteq\{1,\dots,M\}$ contains each coordinate independently with probability $\hat e=2\sqrt{\gamma(1-\gamma)}$.
--   2. It never outputs a codeword $d'\neq d$.
--
--   This is the USD decoder of §3.2: USD on each qubit, then Gaussian elimination on the unerased bits. Theorem 2.7 analyzes its success probability on random $B$.
--
--   Differences from the source:
--   - reading: decoding succeeds precisely when the row-submatrix B_S indexed by the erased set S has full row rank → there is a POVM on the M received qubits, with outcomes Option (𝔽₂^M), whose success on every d ∈ C^⊥ is exactly P_S[B_S full row rank] and which never outputs a wrong codeword; reason: the paper defines the USD decoder through this property (qubit-wise USD, then Gaussian elimination); its circuit is in [CT23], not in the paper
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), §3.2, p.14 and proof of Theorem 2.7, p.16

import Mathlib
import Definitions.Def_DQIShattered_Decoding
import Definitions.Def_DQIShattered_Thresholds

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, §3.2, pp.14 and 16 (the USD decoder).

For every `B ∈ 𝔽₂^{M×N}` and `γ ∈ [0, 1/2]` there is a measurement of the `M` received qubits, with outcomes a
codeword estimate or failure, such that for every `d ∈ C^⊥`, on input `|ψ_{d,γ}⟩`:

1. it outputs `d` with probability exactly `P_S[B_S has full row rank]`, where `S` erases each coordinate
   independently with probability `ê = 2√(γ(1−γ))`;
2. it never outputs a wrong codeword `d' ≠ d`.

**Formalization Note** The measurement is a POVM on `𝔽₂^M` with outcomes `Option (𝔽₂^M)` (`none` = failure);
"decoding succeeds precisely when `B_S` has full row rank" is read as the exact success probability together with
the absence of wrong answers. `1 − rankFailProb` is `∑_S P(S)·[B_S full row rank]`. -/
theorem usd_decoder {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1 / 2) :
    ∃ E : Option (Reg M) → Matrix (Reg M) (Reg M) ℂ, IsPOVM E ∧ ∀ d ∈ dualCode B,
      (expect (E (some d)) (psiState d γ)).re = 1 - rankFailProb B (erasureRate γ) ∧
        ∀ d' : Reg M, d' ≠ d → expect (E (some d')) (psiState d γ) = 0 := by sorry

end DQIShattered
