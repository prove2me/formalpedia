-- Prove2me | Theorems.Thm_BNS2000_theorem_5_1
-- name    : BNS2000.theorem_5_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:08:57.77024+00:00
-- url     : https://prove2.me/theorems/6697cd6f-3349-437a-a835-5aded351f76f
-- title:
--   Bounding Theorem — Polynomial-Time Normalization of Closed Level-1 RA-Terms (Theorem 5.1)
-- statement:
--   Theorem 5.1 (p. 26): Every closed `RA`-term `t` of first-order type `σ₁ → ⋯ → σ_k → τ` normalizes on numerals `n₁, ..., n_k` in polynomial time (`≤ p_t(∑ |n_i|)` steps and register size) via reduction to an equivalent closed `R`-free `RS`-term of length `≤ p_t(∑ |n_i|)`.
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 5, Theorem 5.1, p. 26.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 5.1 (Bounding)** (Section 5, p. 26):
Let `t` be a closed `RA`-term of type `σ₁ → ⋯ → σₖ → τ`, where `σ₁, ..., σₖ, τ` are all
ground types. Then there exists a polynomial `p_t : Nat → Nat` (`IsUnivariatePoly p_t`)
such that for all numerals `n₁, ..., nₖ` of types `σ₁, ..., σₖ` respectively, there exists
a closed `R`-free `RS`-term `u` of type `τ` equivalent to `t n₁ ... nₖ` of length
`|u| ≤ p_t(∑ |nᵢ|)` whose numeral normal form `nf(t n⃗) = nf(u)` is computed by `NFEval`
in at most `p_t(∑ |nᵢ|)` steps using registers of size at most `p_t(∑ |nᵢ|)`. -/
theorem theorem_5_1
    (k : Nat) (σs : Fin k → Ty) (τ : Ty) (t : Term)
    (ht : IsRATerm t)
    (hclosed : IsClosed t)
    (hty : HasType t (Ty.arrMany (List.ofFn σs) τ))
    (hσs : ∀ i : Fin k, (σs i).isGround = true)
    (hτ : τ.isGround = true) :
    ∃ p_t : Nat → Nat,
      IsUnivariatePoly p_t ∧
      ∀ ns : Fin k → Term,
        (∀ i : Fin k, HasType (ns i) (σs i) ∧ isNumeral (ns i) = true) →
        let m := (List.finRange k).foldr (fun i acc => termLength (ns i) + acc) 0
        ∃ (u nf_val : Term) (steps regs maxLen : Nat),
          IsRSTerm u ∧
          isRFree u = true ∧
          IsClosed u ∧
          HasType u τ ∧
          TermEquiv u (Term.appMany t (List.ofFn ns)) ∧
          NFEval u [] nf_val steps regs maxLen ∧
          IsNormalFormOf (Term.appMany t (List.ofFn ns)) nf_val ∧
          isNumeral nf_val = true ∧
          termLength u ≤ p_t m ∧
          steps ≤ p_t m ∧
          regs ≤ p_t m ∧
          maxLen ≤ p_t m := by
  sorry

end BNS2000
