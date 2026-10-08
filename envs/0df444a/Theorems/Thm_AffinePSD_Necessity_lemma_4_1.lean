-- Prove2me | Theorems.Thm_AffinePSD_Necessity_lemma_4_1
-- name    : AffinePSD.Necessity.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:56.697177+00:00
-- url     : https://prove2.me/theorems/39f7046a-51b3-446c-8810-2de23b8ece4d
-- title:
--   Lemma 4.1 — for $x,u\in S_d^+$: $ux=xu=0$ iff $\langle x,u\rangle=0$ iff $u=O\,\mathrm{diag}(0,w)\,O^\top$
-- statement:
--   Let $x, u \in S_d^+$ and let
--   $$x = O\Lambda O^\top = O\,\mathrm{diag}(\lambda_1 > 0, \dots, \lambda_{d-r} > 0, 0, \dots, 0)\,O^\top \qquad (4.1)$$
--   be a diagonalization of $x$, with $0 \le r \le d$ and $O$ orthogonal. Then the following are equivalent:
--
--   1. $ux = xu = 0$;
--   2. $\langle x, u\rangle = 0$;
--   3. $u$ is of the form
--   $$u = O\begin{pmatrix} 0 & 0 \\ 0 & w\end{pmatrix} O^\top \qquad (4.2)$$
--   with $w \in S_r^+$ occupying the lower-right $r \times r$ block.
--
--   This describes the normal directions of the cone at $x$ and is used to translate the admissibility conditions "for all $x, u \in S_d^+$ with $\langle x,u\rangle = 0$" into conditions on zero divisors.
--
--   **Formalization Note.** The diagonalization is passed as data: an orthogonal $O$ ($O^\top O = I$), eigenvalues $\lambda$ positive on the first $d-r$ indices and zero on the last $r$, and $x = O\,\mathrm{diag}(\lambda)\,O^\top$. Statement 3 says that $O^\top u O$ vanishes in every entry with a row or column index among the first $d - r$, and that its lower-right $r\times r$ block is positive semidefinite. The three-way equivalence is stated as $(1 \Leftrightarrow 2) \wedge (2 \Leftrightarrow 3)$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Lemma 4.1 and (4.1)–(4.2), p. 19

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

open Matrix

namespace AffinePSD.Necessity

/-- Lemma 4.1 (arXiv:0910.0137v3, §4, p. 19). Let `x, u ∈ S_d^+` and let
`x = OΛO^⊤ = O diag(λ_1 > 0, …, λ_{d−r} > 0, 0, …, 0) O^⊤` (4.1) be the diagonalization of `x`, with
`r ≥ 0` and `O ∈ O(d)`. Then the following are equivalent:
(i) `ux = xu = 0`; (ii) `⟨x, u⟩ = 0`; (iii) `u = O [[0, 0], [0, w]] O^⊤` (4.2) with `w ∈ S_r^+`.

**Formalization Note.** The diagonalization is data: an orthogonal `O` (`O^⊤O = I`), eigenvalues `lam`
with `lam i > 0` for the first `d − r` indices and `lam i = 0` for the last `r`, and
`x = O diag(lam) O^⊤`. Statement (iii) says `O^⊤ u O` vanishes outside the lower-right `r × r` block
(indices `≥ d − r`) and that block, `w`, is positive semidefinite. The equivalence is stated as
`(i ↔ ii) ∧ (ii ↔ iii)`. -/
theorem lemma_4_1 {d : ℕ} (x u : Mat d) (hx : PSD x) (hu : PSD u) (r : ℕ) (hr : r ≤ d)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (lam : Fin d → ℝ)
    (hlam_pos : ∀ i : Fin d, i.val < d - r → 0 < lam i)
    (hlam_zero : ∀ i : Fin d, d - r ≤ i.val → lam i = 0)
    (hdiag : Matrix.of x = O * Matrix.diagonal lam * Oᵀ) :
    ((mmul u x = 0 ∧ mmul x u = 0) ↔ tr x u = 0) ∧
    (tr x u = 0 ↔
      ((∀ i j : Fin d, (i.val < d - r ∨ j.val < d - r) → (Oᵀ * Matrix.of u * O) i j = 0) ∧
        (Matrix.of fun a b : Fin r =>
          (Oᵀ * Matrix.of u * O) ⟨d - r + a.val, by omega⟩ ⟨d - r + b.val, by omega⟩
          ).PosSemidef)) := by sorry

end AffinePSD.Necessity
