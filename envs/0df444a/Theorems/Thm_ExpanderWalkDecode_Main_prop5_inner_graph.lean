-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop5_inner_graph
-- name    : ExpanderWalkDecode.Main.prop5_inner_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:43.396738+00:00
-- url     : https://prove2.me/theorems/d9bc32c5-f612-4da0-b89d-6e3edafc62a1
-- title:
--   Proposition 5 ([AGHP92]) — explicit small-bias Cayley graphs on $\mathbb F_2^r$, $\lambda_B\le(r-1)2^{-\ell}$
-- statement:
--   There is one program that, for all $r,\ell$ with $1\le\ell\le r/2$, outputs (deterministically, within $K(2^{2\ell}(r+1))^K$ steps) a family of $2^{2\ell}$ distinct generators of $\mathbb F_2^r$ whose Cayley graph, which is undirected and $2^{2\ell}$-regular, has expansion
--   $$\lambda_B\le(r-1)\,2^{-\ell}.$$
--
--   These are the inner graphs of the wide replacement product.
--
--   Differences from the source:
--   - reading: r, ℓ ∈ ℕ with ℓ ≤ r/2 → 1 ≤ ℓ ≤ r/2; reason: ℕ = {1, 2, …}; at ℓ = 0, r = 1 the claim is false: a 1-regular graph on F_2 has eigenvalue ±1 on the nonconstant vector, but the bound is 0
--   - encoding: Cayley(G, U) for a subset U → an injective enumeration u of the generator subset, with domain Fin (2^(2ℓ)); reason: distinct indices name distinct group elements, so degree is the cardinality of the subset as defined on printed p. 21
--   - reading: an explicit construction → one program outputs the generators from (r, ℓ) in time polynomial in 2^{2ℓ}·r; reason: explicit = constructible in polynomial time
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 22 (PDF p. 25), Appendix B.2, Proposition 5

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 5 (The Inner Graph [AGHP92]) (Appendix B.2, p. 22): one program constructs, for
all `r, ℓ` with `1 ≤ ℓ ≤ r/2`, a `2^{2ℓ}`-regular Cayley graph on `F₂^r` (a family of distinct generators of
size `2^{2ℓ}`) with expansion `λ_B ≤ (r - 1) 2^{-ℓ}`; it outputs the generators in time polynomial
in `2^{2ℓ} r`. -/
theorem prop5_inner_graph :
    ∃ (u : ∀ r ℓ : ℕ, Fin (2 ^ (2 * ℓ)) → (Fin r → ZMod 2)) (P : Program) (K : ℝ), Admissible P ∧
      ∀ r ℓ : ℕ, 1 ≤ ℓ → 2 * ℓ ≤ r →
        Function.Injective (u r ℓ) ∧
        (cayley (u r ℓ)).IsExpander (((r : ℝ) - 1) * (2 : ℝ) ^ (-(ℓ : ℝ))) ∧
        RunsWithin P (natPairInput r ℓ) (K * ((2 : ℝ) ^ (2 * ℓ) * ((r : ℝ) + 1)) ^ K)
          (fun out => out = genOut (u r ℓ)) 1 := by sorry

end ExpanderWalkDecode.Main
