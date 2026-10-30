-- Prove2me | Theorems.Thm_AKNMixed_FQP_subroutineGate_single
-- name    : AKNMixed.FQP.subroutineGate_single
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:15.912082+00:00
-- url     : https://prove2.me/theorems/3567d0e2-58b9-47e6-9fd8-c4bcd2358a73
-- title:
--   Lemma 5, Eq. (1) — compact form of the subroutine gate
-- statement:
--   Let $f$ be a probabilistic function from $m$ to $p$ bits and $g_f$ its subroutine gate. For inputs $i_1,i_2\in\{0,1\}^m$,
--
--   $$g_f\circ\bigl(|i_1,0\rangle\langle i_2,0|\bigr)=\begin{cases}\displaystyle\sum_j f_{ij}\,|i,j\rangle\langle i,j| & \text{if } i_1=i_2=i,\\[2mm] \displaystyle\sum_{j_1,j_2} f_{i_1j_1}f_{i_2j_2}\,|i_1,j_1\rangle\langle i_2,j_2| & \text{if } i_1\neq i_2 .\end{cases}$$
--
--   On a classical input the subroutine gate produces the output distribution $f_{i,\cdot}$, and between different inputs it keeps the coherence $f_{i_1j_1}f_{i_2j_2}$. This is the target the circuit constructed in the proof of Theorem 2 is checked against.
--
--   Differences from the source:
--   - encoding: |i, j⟩⟨i', j'| and real probabilities f_{ij} → Matrix.single (i, j) (i', j') 1 on Qubits m × Qubits p, with the probabilities cast to ℂ; reason: Lean convention; same instances
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 5, Eq. (1), p. 10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_ProbFun
import Definitions.Def_AKNMixed_FQP_subroutineGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **Lemma 5 (Eq. (1)): the compact form of a subroutine gate.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 5, Eq. (1), p. 10: "g_f ∘ (|i1, 0⟩⟨i2, 0|) = Σ_j f_ij |i, j⟩⟨i, j| if i1 = i2 = i;
Σ_{j1,j2} f_{i1 j1} f_{i2 j2} |i1, j1⟩⟨i2, j2| if i1 ≠ i2".

For a probabilistic function `f : {0,1}^m → distributions on {0,1}^p` and inputs `i₁, i₂`,
the subroutine gate sends `|i₁, 0⟩⟨i₂, 0|` to `Σ_j f_{i₁ j} |i₁, j⟩⟨i₁, j|` when `i₁ = i₂`, and
to `Σ_{j₁, j₂} f_{i₁ j₁} f_{i₂ j₂} |i₁, j₁⟩⟨i₂, j₂|` when `i₁ ≠ i₂`.

**Formalization Note.** `|i, x⟩⟨i', x'|` is `Matrix.single (i, x) (i', x') 1`, the input register
first; `0` is the all-`false` string. The real probabilities are cast to `ℂ`. -/
theorem subroutineGate_single {m p : ℕ} (f : ProbFun m p) (i₁ i₂ : Qubits m) :
    subroutineGate f (Matrix.single (i₁, (fun _ => false : Qubits p))
        (i₂, (fun _ => false : Qubits p)) 1) =
      if i₁ = i₂ then
        ∑ j : Qubits p, ((f.prob i₁ j : ℝ) : ℂ) • Matrix.single (i₁, j) (i₁, j) 1
      else
        ∑ j₁ : Qubits p, ∑ j₂ : Qubits p,
          ((f.prob i₁ j₁ * f.prob i₂ j₂ : ℝ) : ℂ) • Matrix.single (i₁, j₁) (i₂, j₂) 1 := by sorry

end AKNMixed.FQP
