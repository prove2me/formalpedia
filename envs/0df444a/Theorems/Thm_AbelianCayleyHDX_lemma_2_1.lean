-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_2_1
-- name    : AbelianCayleyHDX.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:32:50.027393+00:00
-- url     : https://prove2.me/theorems/d61e1952-7f06-4fb0-bcc7-83433a0840a8
-- title:
--   Lemma 2.1 — characters diagonalize $\mathrm{Cay}(\mathbb F_2^n,S)$; connected iff $S$ spans
-- statement:
--   Let $\emptyset \ne S \subseteq \mathbb F_2^n \setminus \{0\}$. For $\xi \in \mathbb F_2^n$ let $\chi_\xi(x) = (-1)^{\langle \xi, x\rangle}$. Then:
--   1. the characters are pairwise orthogonal: $\sum_x \chi_\xi(x)\chi_\eta(x) = 0$ for $\xi \ne \eta$;
--   2. they are linearly independent and span the real functions on $\mathbb F_2^n$;
--   3. each is an eigenvector of the normalized adjacency operator $P_S$ of $\mathrm{Cay}(\mathbb F_2^n, S)$:
--   $$P_S \chi_\xi = \Big(\frac{1}{|S|}\sum_{s \in S} \chi_\xi(s)\Big)\chi_\xi ;$$
--   4. $\mathrm{Cay}(\mathbb F_2^n, S)$ is connected if and only if $S$ spans $\mathbb F_2^n$.
--
--   This computes the spectrum of every Cayley graph on $\mathbb F_2^n$ and is used for the link graphs in Lemma 3.7.
--
--   Differences from the source:
--   - encoding: the group $\mathbb F_2^n$ → `Fin n → ZMod 2`; reason: Lean convention; same group
--   - encoding: the characters form an orthogonal eigenbasis of $P_S$ → pairwise orthogonality, linear independence, spanning, and the eigenvalue identity; reason: these four clauses are exactly an orthogonal eigenbasis
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_normAdj
import Definitions.Def_AbelianCayleyHDX_character
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Lemma 2.1** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9). Let `∅ ≠ S ⊆ 𝔽₂ⁿ ∖ {0}` (the standing assumption of
Section 2.3). The characters `χ_ξ(x) = (−1)^{⟨ξ, x⟩}`, `ξ ∈ 𝔽₂ⁿ`, are pairwise orthogonal and form
a basis of the real functions on `𝔽₂ⁿ`; each is an eigenvector of the normalized adjacency operator
`P_S` of `Cay(𝔽₂ⁿ, S)` with `P_S χ_ξ = ((1/|S|) ∑_{s ∈ S} χ_ξ(s)) χ_ξ`; and `Cay(𝔽₂ⁿ, S)` is
connected iff `S` spans `𝔽₂ⁿ`.

**Formalization Note** "Orthogonal eigenbasis" is stated as: pairwise orthogonality for the
counting inner product, linear independence and spanning, and the eigenvalue identity. -/
theorem lemma_2_1 {n : ℕ} (S : Finset (Vec n)) (hS : S.Nonempty) (h0 : (0 : Vec n) ∉ S) :
    (∀ ξ η : Vec n, ξ ≠ η → ∑ x : Vec n, character ξ x * character η x = 0) ∧
    LinearIndependent ℝ (fun ξ : Vec n => character ξ) ∧
    Submodule.span ℝ (Set.range fun ξ : Vec n => character ξ) = ⊤ ∧
    (∀ ξ : Vec n, normAdj S (character ξ) =
      ((1 / (S.card : ℝ)) * ∑ s ∈ S, character ξ s) • character ξ) ∧
    ((cayleyGraph S).Connected ↔ Submodule.span (ZMod 2) (S : Set (Vec n)) = ⊤) := by sorry

end AbelianCayleyHDX
