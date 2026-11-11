-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_theorem_6_5
-- name    : ApprovalCore.HarmonicEntropy.theorem_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:42:54.743197+00:00
-- url     : https://prove2.me/theorems/df649886-8195-4c38-8b6e-4526bc88687e
-- title:
--   Theorem 6.5 — approximate local optima and committees selected by the harmonic entropy rule satisfy core+; the core is non-empty
-- statement:
--   Let $(A, k)$ be an approval-based committee election with $n$ voters, $m$ candidates and $1 \le k \le m-1$, and let $q$ be a quota with
--   $$\frac{n}{k+1} < q \le \frac{n}{k}, \qquad \delta = q - \frac{n}{k+1} > 0 .$$
--   Then:
--
--   (a) every committee $W$ with $|W| = k$ such that
--   $$V(W) > V\big((W \cup \{c\}) \setminus \{d\}\big) - \delta \quad \text{for all } d \in W,\ c \in C \setminus W$$
--   satisfies core+ at quota $q$;
--
--   (b) every committee selected by the harmonic entropy rule (a maximizer of $V$ over $\mathcal W_k$) satisfies core+ at quota $q$;
--
--   (c) some committee $W$ with $|W| = k$ is selected by the harmonic entropy rule and is in the core at quota $q$; in particular the core is non-empty.
--
--   Clause (c) is the paper's headline consequence (p. 2: "This gives (P3) and shows that the harmonic entropy rule satisfies core+. Hence, the core is non-empty."). For the Hare quota $q = n/k$ it settles the existence of the core in approval-based committee elections.
--
--   Differences from the source:
--
--   - encoding: N = [n], C = {c_1, …, c_m}, k ∈ [m − 1], approval sets A_i ⊆ C → Instance n m: voters Fin n, candidates Fin m, A : Fin n → Finset (Fin m), 1 ≤ k and k + 1 ≤ m; reason: same instances; k ∈ [m − 1] is 1 ≤ k ≤ m − 1, i.e. 1 ≤ k and k + 1 ≤ m
--   - encoding: V(W) = max over P124(W) of ∑_i F(r_i, p_i) → V = sSup of the image of P124(W) under ∑_i F(r_i, p_i); reason: the supremum is the paper's maximum once it is attained, which is the milestone section_6_attainment (IsGreatest)
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 14 (PDF 15), Theorem 6.5; p. 2 (PDF 3), 'Hence, the core is non-empty'

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election
import Definitions.Def_ApprovalCore_HarmonicEntropy_Rule

namespace ApprovalCore.HarmonicEntropy

/-- Theorem 6.5 (p. 14) with the headline consequence (p. 2). Let `n/(k+1) < q ≤ n/k` and
`δ = q − n/(k+1)`.
(a) Every `W ∈ W_k` with `V(W) > V(W ∪ {c} \ {d}) − δ` for all `d ∈ W`, `c ∈ C \ W`
satisfies core+.
(b) Every committee selected by the harmonic entropy rule satisfies core+.
(c) Some committee is selected by the rule and lies in the core: the core is non-empty. -/
theorem theorem_6_5 {n m : ℕ} (I : Instance n m) (q : ℝ)
    (hq₁ : (n : ℝ) / ((I.k : ℝ) + 1) < q) (hq₂ : q ≤ (n : ℝ) / (I.k : ℝ)) :
    (∀ W : Finset (Fin m), W.card = I.k →
      (∀ d ∈ W, ∀ c : Fin m, c ∉ W →
        V I.A q W > V I.A q ((insert c W).erase d) - (q - (n : ℝ) / ((I.k : ℝ) + 1))) →
      SatisfiesCorePlus I q W) ∧
    (∀ W : Finset (Fin m), SelectedByRule I q W → SatisfiesCorePlus I q W) ∧
    (∃ W : Finset (Fin m), SelectedByRule I q W ∧ InCore I q W) := by sorry

end ApprovalCore.HarmonicEntropy
