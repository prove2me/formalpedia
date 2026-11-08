-- Prove2me | Theorems.Thm_AffDisp4n_lemma_2_2
-- name    : AffDisp4n.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:33.393168+00:00
-- url     : https://prove2.me/theorems/b638242f-fb5c-4e5f-8748-ce0d481053df
-- title:
--   Lemma 2.2 (existence clause; polynomial-time clause: lemma_2_2_time) — a simple output is constant on an affine subspace of dimension $\ge a-1$
-- statement:
--   Let $P$ be a set of $q$ disjoint pairs of the parameters $u \in \mathbb F_2^m$, let $a = m - q$, and suppose $a > d$. Let $g : \mathbb F_2^m \to \mathbb F_2$ be either
--
--   1. an affine function of the parameters, or
--   2. a literal of an AND of two affine functions: $g(u) = (\ell_1(u) + \alpha)(\ell_2(u) + \beta) + \gamma$ with $\ell_1, \ell_2$ affine and $\alpha, \beta, \gamma \in \mathbb F_2$.
--
--   Then there are a nonempty affine subspace $U \subseteq Z(P)$ with
--   $$
--   \dim U \ge a - 1 \;(\ge d)
--   $$
--   and a constant $b \in \mathbb F_2$ such that $g(u) = b$ for every $u \in U$.
--
--   When the output of the current fair semi-circuit has one of these two forms, Lemma 2.2 ends gate elimination: $\Phi(U)$ is an affine subspace of dimension at least $d$ on which the original circuit is constant.
--
--   **Formalization Note** The lemma is stated for the function $g$ computed by the output. This item is the existence clause. The paper's construction "in polynomial time … represented by a point and a basis" is the companion item `AffDisp4n.lemma_2_2_time`.
--
--   Differences from the source:
--   - generalization: the output of C is (i) an affine function of the parameters or (ii) a literal of an AND-type gate whose two parents are affine functions of the parameters → any g : 𝔽₂ᵐ → 𝔽₂ that is affine or equals (ℓ₁ + α)(ℓ₂ + β) + γ with ℓ₁, ℓ₂ affine; reason: an output of either form computes such a g, so the statement for g specializes to the paper's
--   - reading: we can construct in polynomial time an affine subspace U … represented by a point and a basis → there exists a nonempty affine subspace U; the polynomial-time construction and the representation by a point and a basis are the companion item AffDisp4n.lemma_2_2_time; reason: the existence clause needs no machine or encoding, and it is the part Lemma 4.2 uses; the title names the companion
--   - encoding: a > d and dimension at least a − 1 ≥ d → (d : ℤ) < m − |P| and m − |P| − 1 ≤ finrank U.direction; reason: a = m − q with q = |P|; a − 1 ≥ d follows from the hypothesis
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.5, p.17, Lemma 2.2

import Mathlib
import Definitions.Def_AffDisp4n_IsAffineFn
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_PairsDisjoint

namespace AffDisp4n

/-- **Lemma 2.2** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), p.17). Let `P` be a set of `q` disjoint pairs of the `m` parameters and suppose
`a = m − q > d`. Let `g : 𝔽₂ᵐ → 𝔽₂` be the function computed at the output, of one of the two forms
(i) an affine function of the parameters, or (ii) a literal of an AND-type gate whose two parents are
affine functions `ℓ₁, ℓ₂` of the parameters, i.e. `g = (ℓ₁ + α)(ℓ₂ + β) + γ`. Then there are an affine
subspace `U ⊆ Z(P)` of dimension at least `a − 1 ≥ d` and a constant `b ∈ 𝔽₂` with `g(u) = b` for every
`u ∈ U`.

**Formalization Note** The lemma is stated for the function `g` computed by the output (every output
of the two forms computes such a `g`). This item is the existence clause; the polynomial-time construction and the
representation of `U` by a point and a basis are the companion item `lemma_2_2_time`. `U` is a nonempty Mathlib affine
subspace, and its dimension is that of its direction. -/
theorem lemma_2_2 {m : ℕ} (P : Finset (Sym2 (Fin m))) (hP : PairsDisjoint P) (d : ℕ)
    (had : (d : ℤ) < (m : ℤ) - P.card) (g : (Fin m → ZMod 2) → ZMod 2)
    (hg : IsAffineFn g ∨
      ∃ ℓ₁ ℓ₂ : (Fin m → ZMod 2) → ZMod 2, IsAffineFn ℓ₁ ∧ IsAffineFn ℓ₂ ∧
        ∃ α β γ : ZMod 2, ∀ u, g u = (ℓ₁ u + α) * (ℓ₂ u + β) + γ) :
    ∃ U : AffineSubspace (ZMod 2) (Fin m → ZMod 2), (U : Set (Fin m → ZMod 2)).Nonempty ∧
      (U : Set (Fin m → ZMod 2)) ⊆ Z P ∧
      (m : ℤ) - P.card - 1 ≤ (Module.finrank (ZMod 2) U.direction : ℤ) ∧
      ∃ b : ZMod 2, ∀ u ∈ U, g u = b := by sorry

end AffDisp4n
