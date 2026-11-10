-- Prove2me | Theorems.Thm_EditGV897_Main_choosing_syndrome
-- name    : EditGV897.Main.choosing_syndrome
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:27:13.074831+00:00
-- url     : https://prove2.me/theorems/b71654ba-ebcb-4e08-b1a9-870670a70109
-- title:
--   Lemma 2 — Choosing a syndrome
-- statement:
--   Let $t\ge1$ and let $F$ be an admissible indexed family of $M\ge1$ affine edit maps on $\mathbb F_2^n$. Suppose $G$ has full row rank, with $b=\lceil\log_2(2M)\rceil<n$ rows and $W_G(\mathbb F_2^n)\le2^{n-1}$. The specified deterministic syndrome search returns a minimizing syndrome $\beta^\star\in\mathbb F_2^b$ satisfying
--
--   $$W_G(D_{G,\beta^\star})\le2^{n-b-1},\qquad |D_{G,\beta^\star}|=2^{n-b},\qquad L_G(D_{G,\beta^\star})\ge2^{n-b-1}.$$
--
--   One fixed program realizes this selection within $A(n+M+1)^d$ transitions for uniform $A>0$ and natural $d$, chosen before all inputs. The syndrome is the computed minimizer, not a supplied certificate.
--
--   This is the one-time selection of the shared syndrome used for every message.
--
--   **Formalization Note** Full row rank and the global witness bound are precisely the output of Part 1. The source exponent is $n-b-1$, not an affine expression produced by flattened PDF extraction. No assumption says that the whole selected coset is separated.
--
--   Differences from the source:
--   - encoding: ordered binary words and one-based positions → Fin n → ZMod 2, ordered lists, and zero-based positions; reason: these are order-preserving representations of the same words and legal edits
--   - encoding: an indexed family of affine edit maps → a list with occurrence multiplicity and membership in the canonical legal-script family; reason: equal induced maps remain separately indexed and fixed-point witnesses are excluded
--   - encoding: deterministic polynomial-time algorithms → fixed finite binary tape programs with actual halting executions bounded by positive uniform A(s+1)^d; reason: the fixed-tape bit model preserves polynomial time and charges input, output and all arithmetic work
--   - encoding: a minimizing syndrome and the subsequent coset-size and lower-bound conclusions → the deterministic minimizer together with all three displayed guarantees; reason: the additional explicit clauses are the equations and concluding paragraph on the same page
--   - generalization: the matrix H constructed in Part 1 → any full-row-rank matrix with b=ceil(log₂(2M))<n rows and the same global witness bound; reason: the minimization and averaging argument uses only these Part 1 output properties, all of which the source construction supplies
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Lemma 2, §4.2, printed p. 11 / PDF p. 12

import Definitions.Def_EditGV897_Main_Construction

namespace EditGV897.Main

/-- Lemma 2. The total-witness and rank conditions are Part 1's output. -/
theorem choosing_syndrome :
    ∃ (selector : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length = checkRows F.length → G.length < n →
        FullRowRank G → witnessSum F G Finset.univ ≤ 2 ^ (n - 1) →
        let β := chooseSyndrome F G
        β.length = G.length ∧
        (∀ γ : List Bit, γ.length = G.length →
          witnessSum F G (coset G β) ≤ witnessSum F G (coset G γ)) ∧
        witnessSum F G (coset G β) ≤ 2 ^ (n - G.length - 1) ∧
        (coset G β).card = 2 ^ (n - G.length) ∧
        (2 ^ (n - G.length - 1) : ℤ) ≤ signedBound F G (coset G β) ∧
        Runs selector (syndromeInput F G) (bitCode β) (polyBudget A d (n + F.length)) := by sorry

end EditGV897.Main
