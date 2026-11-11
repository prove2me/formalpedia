-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_6_4
-- name    : FOMCMonDep.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:23.936816+00:00
-- url     : https://prove2.me/theorems/71572f49-190f-43e8-97eb-13bb3e5ecc63
-- title:
--   Lemma 6.4 — a chain of length $\ell$ gives, in time $O(\ell n^3)$, a construction sequence of radius-$r$ width $w_r$ that is radius-$r$ definable with $2\ell+1$ predicates
-- statement:
--   For every $n$-vertex graph $G$ and every chain of $G$ of length $\ell$ there is a construction sequence $G_1,\dots,G_\lambda$ of $G$ such that the following holds for all $r\ge1$. Let $k_r$ be the radius-$(5r+1)$ width of the chain and $w_r=k_r\cdot\pi_G(k_r)$.
--
--   1. The construction sequence has radius-$r$ width at most $w_r$ and length $\lambda\le O(nw_1)$.
--   2. For every $t\in[\lambda-1]$ and $v\in V(G)$, the induced partial graph $G_t[\mathrm{Ball}^{G_{t+1}}_r(v)]$ is definable in some expansion of $G$ with $2\ell+1$ unary predicates, using formulas of quantifier rank $7$ with $w_r$ parameters.
--   3. The construction sequence can be computed in time $O(\ell n^3)$, given $G$ and its chain.
--
--   This is the main technical result of Part II; with Theorem 6.3 it gives Theorem 4.7.
--
--   **Formalization Note** There is no class hypothesis. One program (absolute constants) takes the adjacency matrix of $G$ and the code of the chain, halts within $a_1\ell n^3+b_1$ steps, and outputs the code of one construction sequence satisfying items 1 and 2 for all $r\ge1$ simultaneously; this also gives the existence claim.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a construction sequence G1, …, Gλ of partial graphs → the list of its λ−1 steps on colors named by naturals, from G1 with color v = v; reason: Part III's own representation with named colors; any naming of the singleton parts is equivalent
--   - reading: using formulas of quantifier rank 7 → quantifier rank at most 7; reason: a formula of smaller rank pads to rank 7 with a dummy quantifier
--   - encoding: O(n w1), O(ℓ n³) → a0·(n·w1) + b0 and a1·ℓ·n³ + b1 with absolute constants; reason: the asymptotic convention of §3, p.11, for an unsubscripted O
--   - encoding: G and its chain as input; the construction sequence as output → graphInput G followed by chainCode (ℓ, then ℓ blocks of n bits); the output cells begin with seqCode of the sequence; reason: fixed input/output layout of the mission; the paper fixes none
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 6.4, p.29 (PDF 31)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_Chain
import Definitions.Def_FOMCMonDep_nbhdComplexity
import Definitions.Def_FOMCMonDep_RadiusDefinable

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- **Lemma 6.4.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §6, p.29 (PDF 31); restated with its proof p.37 (PDF 39): "For every
n-vertex graph G and its chain of length ℓ there is a construction sequence G1, . . . , Gλ of G such that the following
properties hold for all r ⩾ 1. Let k_r denote the radius-(5r + 1) width of the chain and w_r := k_r · π_G(k_r).
1. The resulting construction sequence has radius-r width at most w_r and length λ ⩽ O(nw1).
2. For every t ∈ [λ − 1] and v ∈ V(G), the induced partial graph Gt[Ball^{Gt+1}_r(v)] is definable in some expansion
of G with 2ℓ + 1 unary predicates, using formulas of quantifier rank 7 with w_r parameters.
3. The construction sequence can be computed in time O(ℓn³), given G and its chain."

**Formalization Note.** No class hypothesis: every graph and every chain. One program (with word-size factor `bw`)
and absolute constants (the unsubscripted `O`): on input `graphInput G` followed by the chain's code it accepts within
`a₁ · ℓ · n³ + b₁` steps, and its output is the code of **one** construction sequence that satisfies items 1–2 for
**all** `r ⩾ 1` at once; this also gives the existence claim. `k_r` is `chainWidth G S (5r + 1)`, `π_G` is the local
`nbhdComplexity` (p.11). Item 1's width is the §2 radius-`r` width (parts meeting the ball), `radiusWidth`. Item 2 is
Definition 4.6 (`RadiusDefinable`, "quantifier rank 7" read as "at most 7"). -/
theorem lemma_6_4 :
    ∃ a₀ b₀ a₁ b₁ : ℕ, ∃ (P : List Instr) (bw : ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        ∀ W : ℕ, WordSizeOK bw (MonDepMW.graphInput G ++ chainCode S) W →
          MonDepMW.RunsWithin P W (a₁ * S.length * n ^ 3 + b₁) (MonDepMW.graphInput G ++ chainCode S) fun out =>
            ∃ seq : List Step, Emits out (seqCode seq) ∧ IsConstructionSeq G seq ∧
              seqLength seq ≤
                a₀ * (n * (chainWidth G S (5 * 1 + 1) * nbhdComplexity G (chainWidth G S (5 * 1 + 1)))) + b₀ ∧
              ∀ r : ℕ, 1 ≤ r →
                radiusWidth (n := n) seq r ≤
                    chainWidth G S (5 * r + 1) * nbhdComplexity G (chainWidth G S (5 * r + 1)) ∧
                  RadiusDefinable G seq r (2 * S.length + 1)
                    (chainWidth G S (5 * r + 1) * nbhdComplexity G (chainWidth G S (5 * r + 1))) 7 := by sorry

end FOMCMonDep
