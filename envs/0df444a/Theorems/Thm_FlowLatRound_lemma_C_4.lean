-- Prove2me | Theorems.Thm_FlowLatRound_lemma_C_4
-- name    : FlowLatRound.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:34.755502+00:00
-- url     : https://prove2.me/theorems/d1576b41-c621-4a19-83eb-ad592ed225bb
-- title:
--   Lemma C.4 — trees containing a forest: $\sum_{T\supseteq F}\prod_i z_i^{\deg_T(i)-\deg_F(i)}=\big(\prod_jW_j\big)(z_1+\dots+z_n)^{c-2}$
-- statement:
--   Let $F$ be a spanning forest of $[n]$ with components $V_1,\dots,V_c$, $c\ge2$, and put $W_j=\sum_{i\in V_j}z_i$. Then
--   $$\sum_{T\supseteq F}\prod_iz_i^{\deg_T(i)-\deg_F(i)}=\Big(\prod_{j=1}^cW_j\Big)(z_1+\dots+z_n)^{c-2},$$
--   the sum over labeled trees $T$ on $[n]$ containing $F$, as an identity of polynomials with integer coefficients.
--
--   This weighted Cayley formula drives the exact cycle-length law of Proposition C.7.
--
--   Differences from the source:
--   - encoding: vertices [n] and edges labeled 1..m → Fin n and Fin m (0-indexed); reason: Lean convention; relabeling changes no instance
--   - encoding: identity in variables z_1, …, z_n → identity in MvPolynomial (Fin n) ℤ; reason: a polynomial identity over ℤ is equivalent to the identity for all real (or complex) z
--   - encoding: labeled trees and spanning forests of [n] → loopless edge sets of Sym2 (Fin n) with n − 1 edges connecting [n], resp. with #edges + #components = n; reason: standard characterizations
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.4, p.24 (PDF 26)

import Mathlib
import Definitions.Def_FlowLatRound_LabeledTree

namespace FlowLatRound

/-- Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027 submission,
sha256 35bd3e4b…aeac), Lemma C.4, p.24 (PDF 26). Trees containing a forest: let `F` be a spanning forest of
`[n]` with components `V₁, …, V_c`, `c ≥ 2`, and `W_j = Σ_{i ∈ V_j} z_i`. Then
`Σ_{T ⊇ F} Π_i z_i^{deg_T(i) − deg_F(i)} = (Π_j W_j) (z₁ + ⋯ + z_n)^{c−2}`, the sum over labeled
trees `T` on `[n]` containing `F`.

**Formalization Note.** Stated as an identity of polynomials in `ℤ[z₁, …, z_n]` (which implies it
for all real `z`). `deg_T(i) − deg_F(i)` is a natural subtraction, exact because `F ⊆ T`. -/
theorem lemma_C_4 {n : ℕ} (F : Finset (Sym2 (Fin n))) (hF : IsForest F)
    (hc : 2 ≤ (comps F).card) :
    ∑ t ∈ (Finset.univ : Finset (LTree n)).filter (fun t => F ⊆ t.1),
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (degE t.1 i - degE F i) =
      (∏ C ∈ comps F, ∑ i ∈ C, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)) *
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)) ^ ((comps F).card - 2) := by sorry

end FlowLatRound
