-- Prove2me | Theorems.Thm_AlgSemNondet_Main_theorem_4_5
-- name    : AlgSemNondet.Main.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:47:38.365198+00:00
-- url     : https://prove2.me/theorems/99dbe03a-0c12-45c0-9ce9-7baca246d41b
-- title:
--   Theorem 4.5 — incommensurability cannot be internalized
-- statement:
--   Let $M$ be a classical Turing machine whose alphabet $\Gamma$ contains the blank $B$ and at least four data symbols different from $B$, and let $\mathfrak P$ be any intrinsic property (Definition 4.2). Then there exist an algebraic encoding $\varepsilon_0 : \Gamma \setminus \{B\} \to \overline{\mathbb Q}$ and an input $w \in (\Gamma \setminus \{B\})^+$ (nonempty, every letter non-blank) such that
--   $$\mathfrak P(M, w) \;\not\Longleftrightarrow\; \text{“}M \text{ associates } \varepsilon\text{-incommensurable elements on } w\text{”}.$$
--
--   Differences from the source:
--   - reading: M appears free in the statement → the claim is made for every machine M (for the given M, ∃ ε, w); reason: the literal per-machine reading, which is the stronger one (finding I2: the printed proof reaches only the ∃M form)
--   - reading: ε : Γ∖{B} → 𝔸 for a set 𝔸 ⊆ ℚ̄ of algebraic numbers (Definition 4.4), 𝔸 not fixed by the theorem → ε₀ takes values in the complex numbers algebraic over ℚ, i.e. 𝔸 = ℚ̄; reason: ε is existentially quantified, so choosing ε into some 𝔸 ⊆ ℚ̄ is the same as choosing it into ℚ̄; a fixed small 𝔸 such as {1} would make the theorem false
--   - encoding: at least four data symbols different from B → 4 ≤ Fintype.card {c : Γ // c ≠ B}; reason: same condition
--   - encoding: w ∈ (Γ∖{B})⁺ → w : List Γ with w ≠ [] and every letter ≠ B; reason: same set of words
--   - encoding: "M associates ε-incommensurable elements on w" → ε.AssociatesIncommensurable w, with no machine argument; reason: Definition 4.4 makes the predicate depend only on w and ε
--   - encoding: 𝔓 a property of a machine on an input → a predicate on machines with fixed state type Q, alphabet Γ and blank B and on all words over Γ; reason: M_π stays in this class, and a property intrinsic on the inputs (Γ∖{B})⁺ extends (false elsewhere) to one intrinsic on all words, since π preserves that set
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Theorem 4.5, p.17, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine
import Definitions.Def_AlgSemNondet_Main_relabel
import Definitions.Def_AlgSemNondet_Main_IsIntrinsic
import Definitions.Def_AlgSemNondet_Main_Incommensurable
import Definitions.Def_AlgSemNondet_Main_AlgebraicEncoding

namespace AlgSemNondet.Main

/-- Theorem 4.5 (incommensurability cannot be internalized). Let the alphabet `Γ` of a classical
Turing machine `M` contain the blank `B` and at least four data symbols different from `B`, and
let `P` be any intrinsic property. Then there exist an algebraic encoding `ε` and an input
`w ∈ (Γ \ {B})⁺` such that `P(M, w)` is not equivalent to "`M` associates `ε`-incommensurable
elements on `w`". -/
theorem theorem_4_5 {Q Γ : Type*} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    {B : Γ} (hΓ : 4 ≤ Fintype.card {c : Γ // c ≠ B})
    (M : TuringMachine Q Γ B) (P : TuringMachine Q Γ B → List Γ → Prop)
    (hP : IsIntrinsic P) :
    ∃ (ε : AlgebraicEncoding Γ B) (w : List Γ), w ≠ [] ∧ (∀ c ∈ w, c ≠ B) ∧
      ¬ (P M w ↔ ε.AssociatesIncommensurable w) := by sorry

end AlgSemNondet.Main
