-- Prove2me | Theorems.Thm_CardinalMatching_lemma_6
-- name    : CardinalMatching.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:23.713821+00:00
-- url     : https://prove2.me/theorems/8465a13d-e8fd-4876-befd-0005e3395d70
-- title:
--   Lemma 6: Pareto-optimal iff weighted-welfare maximizer; weights computable in polynomial time
-- statement:
--   Let $A$ and $G$ be finite sets with $|A|=|G|$ and let $u_{ij}\ge 0$. For $x^\star\in P_{\mathrm{PM}}$:
--
--   1. $x^\star$ is Pareto-optimal if and only if there exist weights $\alpha_i>0$ ($i\in A$) such that $x^\star$ maximizes
--   $$
--   \varphi(x)=\sum_{i\in A}\alpha_i\,u_i\cdot x_i
--   $$
--   over all $x\in P_{\mathrm{PM}}$;
--   2. if $x^\star$ is rational, such $\alpha$ can be computed in polynomial time: there is one polynomial-time algorithm that, given $n$, rational non-negative utilities $u$ and a rational Pareto-optimal $x^\star\in P_{\mathrm{PM}}$ in binary, outputs rational weights $\alpha>0$ for which $x^\star$ maximizes $\varphi$.
--
--   This is the scalarization of Pareto-optimality used in Step 2 of the reduction and in Theorem 7.
--
--   **Formalization Note** The algorithm is a Cook Turing machine (`CookPvsNP.PolyTimeComputable`) on the codes `encRatMatrix n u ++ encRatMatrix n x⋆` and `encRatVec n α`.
--
--   Differences from the source:
--   - encoding: "α can be computed in polynomial time" (no model of computation stated) → a polynomial-time map on Cook's Turing machines from the binary codes of (n, u, x⋆) to the code of α; reason: standard reading of polynomial-time computation on rational data
--   - reading: "if x⋆ is rational" (utilities not mentioned) → the computability clause takes rational u and rational x⋆ as input; reason: an algorithm needs finite input; the paper's computational instances have rational utilities (p.2)
--   - generalization: rational, non-negative utilities (p.2) → in the equivalence, any real non-negative utilities; reason: the equivalence does not use rationality; it specializes to the rational case
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 6, p.6 (proof in Appendix A, p.27)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CardinalMatching_IsFracPerfectMatching
import Definitions.Def_CardinalMatching_IsParetoOptimal
import Definitions.Def_CardinalMatching_weightedWelfare
import Definitions.Def_CardinalMatching_encRatMatrix

namespace CardinalMatching

/-- **Lemma 6** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, §2.1, p.6; proof in App. A, p.27): "x⋆ ∈ P_PM is Pareto-optimal if and
only if there exist positive (αi)i∈A such that x⋆ maximizes φ(x) := ∑_{i∈A} αi ui · xi over all
x ∈ P_PM. Moreover, if x⋆ is rational, α can be computed in polynomial time."

The first conjunct is the equivalence, for any finite sets of agents `A` and goods `G` with
`|A| = |G|` and non-negative utilities. The second is the computability clause: one
polynomial-time map (Cook's Turing machines) sends the binary code of any rational instance
`(n, u)` together with any rational Pareto-optimal `x⋆ ∈ P_PM` to the code of positive rational
weights `α` for which `x⋆` maximizes `φ` over `P_PM`.

**Formalization Note** In the computability clause agents and goods are `Fin n` and the inputs
are rational and binary-encoded (`encRatMatrix`, `encRatVec`); the input is the pair `(u, x⋆)`. -/
theorem lemma_6 :
    (∀ (A G : Type) [Fintype A] [Fintype G], Fintype.card A = Fintype.card G →
      ∀ (u : A → G → ℝ), (∀ i j, 0 ≤ u i j) →
      ∀ (xs : A → G → ℝ), IsFracPerfectMatching xs →
        (IsParetoOptimal u xs ↔
          ∃ α : A → ℝ, (∀ i, 0 < α i) ∧
            ∀ x, IsFracPerfectMatching x → weightedWelfare α u x ≤ weightedWelfare α u xs)) ∧
    ∃ F : List Bool → List Bool, CookPvsNP.PolyTimeComputable F ∧
      ∀ (n : ℕ) (u xs : Fin n → Fin n → ℚ), 1 ≤ n → (∀ i j, 0 ≤ u i j) →
        IsFracPerfectMatching (fun i j => (xs i j : ℝ)) →
        IsParetoOptimal (fun i j => (u i j : ℝ)) (fun i j => (xs i j : ℝ)) →
        ∃ α : Fin n → ℚ, (∀ i, 0 < α i) ∧
          (∀ x, IsFracPerfectMatching x →
            weightedWelfare (fun i => (α i : ℝ)) (fun i j => (u i j : ℝ)) x ≤
              weightedWelfare (fun i => (α i : ℝ)) (fun i j => (u i j : ℝ))
                (fun i j => (xs i j : ℝ))) ∧
          F (encRatMatrix n u ++ encRatMatrix n xs) = encRatVec n α := by sorry

end CardinalMatching
