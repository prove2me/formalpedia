-- Prove2me | Theorems.Thm_EditPRC_Boost_theorem_3_16
-- name    : EditPRC.Boost.theorem_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:08:36.36945+00:00
-- url     : https://prove2.me/theorems/d67aea52-d319-48da-a794-c600503ad965
-- title:
--   Theorem 3.16 ([HS21]) — repositioning an edited self-matching string in time $O(n^2/\sqrt{\varepsilon})$ recovers a $1-\delta-3\sqrt{\varepsilon}$ fraction of its symbols
-- statement:
--   Let $\Gamma$ be a finite alphabet. There is a constant $C$ such that for every $\varepsilon$ there is a program of the unit-cost real RAM with the following property. Let $s\in\Gamma^n$ be $\varepsilon$-self-matching, and let $s'\in\Gamma^{n'}$ arise from $s$ by $d_d$ deletions and $d_i\le n$ insertions, through a process with surviving positions $\mathrm{surv}$ and order-preserving placement $\mathrm{emb}$ (so the corresponding symbol of a surviving $s_i$ is $s'_{\mathrm{emb}(i)}$). Run on $(s,s')$ alone, the program halts within
--   $$C\,\frac{n^2}{\sqrt{\varepsilon}}+C\ \text{steps}$$
--   with a matching (no position of $s'$ is matched to two positions of $s$) in which at least
--   $$\bigl(1-\delta-3\sqrt{\varepsilon}\bigr)\,n,\qquad \delta=\frac{d_d+d_i}{n},$$
--   of the surviving symbols $s_i$ are matched to their corresponding symbols $s'_{\mathrm{emb}(i)}$.
--
--   In the boost of Theorem 3.12 this turns edits of the synchronization-string block into a small fraction of substitutions, which an ordinary error-correcting code then removes.
--
--   Differences from the source:
--   - reading: "an algorithm running in time $O(n^2/\sqrt\varepsilon)$" → a program of the published unit-cost real RAM `SmaleNinth_RealRAM` on the memory layout $M[0]=n$, $M[1]=n'$, $M[2+i]=1+\mathrm{index}(s_i)$, $M[2+n+j]=1+\mathrm{index}(s'_j)$, halting (accepting) within $Cn^2/\sqrt\varepsilon+C$ steps with $C$ depending only on $\Gamma$, the program depending on $\varepsilon$; reason: the source counts LCS computations of $O(n^2)$ unit-cost steps; the additive constant is the usual meaning of $O(\cdot)$ at small $n$.
--   - reading: "after performing $d_i$ insertions and $d_d$ deletions", "matched to their corresponding symbol" → a process given by surviving positions and an order-preserving embedding with $|\mathrm{surv}|+d_d=n$, $|\mathrm{surv}|+d_i=n'$; a surviving $s_i$ counts when the output matches $i$ to $\mathrm{emb}(i)$; the output is read from cells $M[-1-i]=j+1$ and must not match two positions of $s$ to one position of $s'$; reason: the source's matching relation made explicit; the process is arbitrary and unknown to the program.
--   - encoding: strings → maps `Fin n → Γ`, positions from $0$; reason: Lean convention.
--   - generalization: $\varepsilon>0$ (implicit: $\sqrt\varepsilon$ in a denominator) → any real $\varepsilon$; reason: for $\varepsilon\le0$ no string is $\varepsilon$-self-matching and the statement is vacuous, so on $\varepsilon>0$ it is the source's.
--
--   **Formalization Note.** No sign condition on $\varepsilon$ is imposed: for $\varepsilon\le0$ no string is $\varepsilon$-self-matching and the statement is vacuous. For $n=0$ the guarantee reads $0\le$ count. Counts $d_d,d_i$ are the net counts of the process, so a symbol inserted and deleted again is not counted, which only strengthens the guarantee.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 25, Theorem 3.16 ([HS21]), with Definition 3.13

import Mathlib
import Definitions.Def_EditPRC_Boost_SelfMatching

open Classical

namespace EditPRC.Boost

/-- **Theorem 3.16 ([HS21]).** For every finite alphabet `Γ` there is a constant `C` such that for
every `ε` some unit-cost real-RAM program, given `s ∈ Γ^n` and `s' ∈ Γ^{n'}` only, halts
within `C n²/√ε + C` steps and outputs a matching (a partial injection from positions of `s` to
positions of `s'`) with the following property: whenever `s` is `ε`-self-matching and `s'` arises
from `s` by `d_d` deletions and `d_i ≤ n` insertions, at least a `1 − δ − 3√ε` fraction of the
`n` symbols of `s` are matched to their own copies in `s'`, where `δ = (d_d + d_i)/n`. -/
theorem theorem_3_16 (Γ : Type) [Fintype Γ] :
    ∃ C : ℝ, ∀ ε : ℝ, ∃ R : SmaleNinth.RAMProgram,
      ∀ (n n' : ℕ) (s : Fin n → Γ) (s' : Fin n' → Γ) (dd di : ℕ) (surv : Finset (Fin n))
        (emb : Fin n → Fin n'),
        IsSelfMatching ε s → IsInsDel s s' dd di surv emb → di ≤ n →
        ∃ t : ℕ, (t : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.sqrt ε + C ∧
          SmaleNinth.RAMHaltedWith R (SmaleNinth.RAMRun R (ramInput2 s s') t) true ∧
          (∀ i₁ i₂ j : ℕ, i₁ < n → i₂ < n → j < n' →
            RAMMatches (SmaleNinth.RAMRun R (ramInput2 s s') t) i₁ j →
            RAMMatches (SmaleNinth.RAMRun R (ramInput2 s s') t) i₂ j → i₁ = i₂) ∧
          (1 - ((dd : ℝ) + di) / n - 3 * Real.sqrt ε) * n ≤
            ((surv.filter (fun i : Fin n => RAMMatches (SmaleNinth.RAMRun R (ramInput2 s s') t)
              (i : ℕ) (emb i : ℕ))).card : ℝ) := by sorry

end EditPRC.Boost
