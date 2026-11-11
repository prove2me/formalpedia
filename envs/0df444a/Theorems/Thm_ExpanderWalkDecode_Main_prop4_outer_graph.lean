-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop4_outer_graph
-- name    : ExpanderWalkDecode.Main.prop4_outer_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:55.218905+00:00
-- url     : https://prove2.me/theorems/cab4bf9c-d501-4ef1-adfc-fe6b729300cb
-- title:
--   Proposition 4 ([Alo21]) — explicit locally invertible outer expanders of every degree, $\lambda_A\le8/\sqrt d$
-- statement:
--   There is one program that, for all $n$ and $d\ge1$, outputs (deterministically, within $K((n+1)(d+1))^K$ steps for a constant $K$) the rotation table of a graph $A_{n,d}$ that is undirected, $d$-regular and locally invertible, has expansion
--   $$\lambda_A\le\frac{8}{\sqrt d},$$
--   and has $n(1+o_n(1))$ vertices: for every $d$ and $\eta>0$ there is $n_0$ with $n\le|A_{n,d}|\le(1+\eta)n$ for $n\ge n_0$.
--
--   These are the outer graphs of the wide replacement product.
--
--   Differences from the source:
--   - reading: an explicit construction → one program computes the rotation table of A_{n,d} from (n, d) in time polynomial in n·d; reason: explicit = constructible in polynomial time
--   - reading: n·(1 + o_n(1)) vertices → n ≤ |A_{n,d}| ≤ (1+η)n for n ≥ n₀(d, η); reason: the construction embeds [n] into A (§4, step 1), so |A| ≥ n
--   - encoding: d ∈ ℕ → d ≥ 1; reason: the normalized adjacency of a 0-regular graph and 8/√0 are undefined
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 22 (PDF p. 25), Appendix B.1, Proposition 4

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 4 (The Outer Graph [Alo21]) (Appendix B.1, p. 22): one program constructs, for
all `n` and `d ≥ 1`, an undirected `d`-regular locally invertible graph `A_{n,d}` with
`n (1 + o_n(1))` vertices (at least `n`) and expansion `λ_A ≤ 8/√d`; it outputs the rotation table
in time polynomial in `n d`. -/
theorem prop4_outer_graph :
    ∃ (nA : ℕ → ℕ → ℕ) (G : ∀ n d : ℕ, RotGraph (Fin (nA n d)) (Fin d)) (P : Program) (K : ℝ),
      Admissible P ∧
      (∀ d : ℕ, 1 ≤ d → ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        n ≤ nA n d ∧ (nA n d : ℝ) ≤ (1 + η) * n) ∧
      ∀ n d : ℕ, 1 ≤ d →
        (G n d).LocallyInvertible ∧ (G n d).IsExpander (8 / Real.sqrt d) ∧
        RunsWithin P (natPairInput n d) (K * (((n : ℝ) + 1) * ((d : ℝ) + 1)) ^ K)
          (fun out => out = rotTableOut (G n d)) 1 := by sorry

end ExpanderWalkDecode.Main
