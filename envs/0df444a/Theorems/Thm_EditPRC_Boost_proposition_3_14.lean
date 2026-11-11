-- Prove2me | Theorems.Thm_EditPRC_Boost_proposition_3_14
-- name    : EditPRC.Boost.proposition_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:08:40.8312+00:00
-- url     : https://prove2.me/theorems/640374b1-54c1-4b83-b66b-d0fd4cf3f775
-- title:
--   Proposition 3.14 — a uniformly random string in $\Gamma^n$ is $\varepsilon$-self-matching with probability $\ge 1-2^{-\varepsilon n}$ when $|\Gamma|\ge 2e^2\varepsilon^{-2}$
-- statement:
--   Let $\Gamma$ be a finite alphabet, $\varepsilon$ a real number and $n\ge0$. If $|\Gamma|\ge 2e^2\varepsilon^{-2}$, then a string $s$ drawn uniformly from $\Gamma^n$ is $\varepsilon$-self-matching (Definition 3.13: no monotone off-diagonal self-matching of size $t\ge\varepsilon n$) with probability
--   $$\Pr_{s\sim\mathrm{Unif}(\Gamma^n)}\bigl[s\ \text{is}\ \varepsilon\text{-self-matching}\bigr]\ \ge\ 1-2^{-\varepsilon n}.$$
--
--   This is why a random, and hence a pseudorandom, string over a large enough constant alphabet can serve as the synchronization string of the boost in Theorem 3.12.
--
--   Differences from the source:
--   - encoding: "a random string in $\Gamma^n$" → the uniform distribution on maps `Fin n → Γ`, probability $=$ (number of $\varepsilon$-self-matching strings)$/|\Gamma|^n$; reason: Lean convention; same distribution.
--   - generalization: $\varepsilon>0$ (implicit: $\varepsilon^{-2}$, "$\varepsilon$-self-matching") → any real $\varepsilon$, any $n\ge0$; reason: the extra instances $\varepsilon\le0$ are trivially true (no string is $\varepsilon$-self-matching and $1-2^{-\varepsilon n}\le0$), so on $\varepsilon>0$ the statement is the source's.
--
--   **Formalization Note.** No sign condition on $\varepsilon$ is imposed. For $\varepsilon\le0$ no string is $\varepsilon$-self-matching (the empty matching has size $0\ge\varepsilon n$) and the bound $1-2^{-\varepsilon n}\le0$ holds trivially. In Lean $\varepsilon^{-2}$ is `ε ^ (-2 : ℤ)`, which is $0$ at $\varepsilon=0$.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 25, Proposition 3.14 (with Definition 3.13)

import Mathlib
import Definitions.Def_EditPRC_Boost_Machine
import Definitions.Def_EditPRC_Boost_SelfMatching

namespace EditPRC.Boost

/-- **Proposition 3.14.** A uniformly random string in `Γ^n` is `ε`-self-matching with probability
at least `1 − 2^{−εn}` as long as `|Γ| ≥ 2e²ε^{−2}`. -/
theorem proposition_3_14 (Γ : Type) [Fintype Γ] (ε : ℝ)
    (hΓ : 2 * Real.exp 2 * ε ^ (-2 : ℤ) ≤ (Fintype.card Γ : ℝ)) (n : ℕ) :
    1 - (2 : ℝ) ^ (-(ε * n)) ≤ unifProb (fun s : Fin n → Γ => IsSelfMatching ε s) := by sorry

end EditPRC.Boost
