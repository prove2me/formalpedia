-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_5_3
-- name    : BorderDiffEq.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:11.211194+00:00
-- url     : https://prove2.me/theorems/1fca0f6a-b416-4ab3-86e3-69b0877dec8f
-- title:
--   Lemma 5.3 — $D^a\Phi_y(T)/\Phi_y(T)\bmod z^{d+1}$ has a $\Sigma\wedge\Sigma$ circuit of top fan-in $O(d^{3a+1})$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $K$ be a field of characteristic zero, $1\le a\le d$, and $T=\prod_{j=1}^d\ell_j$ with nonzero affine linear $\ell_j\in K[x_1,\dots,x_n]$. Let $K(y)$ be the field of rational functions in $y$, and view $\Phi_y(T)=T(y+zx)$ in $K(y)[x][z]$. Then the truncated ratio
--   $$
--   Q\ \equiv\ \frac{D^a\Phi_y(T)}{\Phi_y(T)}\pmod{z^{d+1}},\qquad \deg_zQ\le d,
--   $$
--   a polynomial in $K(y)[x,z]$, is computed by a $\Sigma\wedge\Sigma$ circuit over $K(y)$ in the variables $(z,x)$ of top fan-in at most
--   $$
--   C\cdot d^{\,3a+1}.
--   $$
--   These truncated logarithmic derivatives are the entries of the normalized matrix in the proof of Proposition 5.4.
--
--   **Formalization Note** The ratio modulo $z^{d+1}$ is the unique $Q$ with $\deg_zQ\le d$ and $\Phi_y(T)\,Q\equiv D^a\Phi_y(T)\pmod{z^{d+1}}$; it is unique because $\Phi_y(T)$ equals $T(y)\ne0$ at $z=0$. The variables $(z,x)$ are `Option (Fin n)` with `none` $=z$, transported by `MvPolynomial.optionEquivLeft`. The circuit is exact (not a border circuit), with exponents unrestricted.
--
--   Differences from the source:
--   - reading: top fan-in $O(d^{3a+1})$ for $1\le a\le d$ → $C\cdot d^{3a+1}$ with one absolute $C$, quantified before the field and all parameters; reason: the uniform constant is the stronger reading of $O(\cdot)$; it holds (the term count is at most $2d\,(6e^2d^3/a^3)^a\le 89\,d^{3a+1}$)
--   - reading: $\ell_j$ "linear polynomials" → affine linear $\ell_j$; reason: the proof writes $\ell_j=c_j+\tilde\ell_j$; affine forms include homogeneous ones, so this is the stronger reading
--   - encoding: $\ell_j$ unrestricted → $\ell_j\neq0$; reason: if some $\ell_j=0$ then $\Phi_y(T)=0$ and the ratio is undefined
--   - encoding: $D^a\Phi_y(T)/\Phi_y(T)\bmod\langle z^{d+1}\rangle$ → the unique $Q$ with $\deg_zQ\le d$ and $\Phi_y(T)Q\equiv D^a\Phi_y(T)\pmod{z^{d+1}}$; reason: $\Phi_y(T)$ is a unit modulo $z$ over $K(y)[x]$, so the truncated quotient is this $Q$
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 5.3, p.32 (proof pp.33–34)

import Mathlib
import Definitions.Def_BorderDiffEq_AffineForm
import Definitions.Def_BorderDiffEq_SigmaWedgeSigma
import Definitions.Def_BorderDiffEq_shift
import Definitions.Def_BorderDiffEq_yToFrac

namespace BorderDiffEq

/-- **Lemma 5.3 (truncated higher logarithmic derivative of a product of affine forms)**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Lemma 5.3, p.32). If
`T := ∏_{j=1}^d ℓⱼ` with `ℓⱼ ∈ F[x]` affine linear, then `D^a(Φ_y(T)) / Φ_y(T) mod ⟨z^{d+1}⟩`, a
polynomial in `F(y)[x, z]`, can be computed by a Σ∧Σ circuit of top fan-in `O(d^{3a+1})`, for
`1 ≤ a ≤ d`.

**Formalization Note.** One absolute constant `C`, before the field and every parameter, reads
`O(·)` (uniform in `a` and `d`). Any field `K` of characteristic zero. The ratio modulo `z^{d+1}`
is the unique `Q ∈ K(y)[x][z]` with `deg_z Q ≤ d` and `Φ_y(T)·Q ≡ D^a Φ_y(T) (mod z^{d+1})`
(unique because `Φ_y(T)` at `z = 0` is `T(y) ≠ 0`); `K(y) = FractionRing (MvPolynomial (Fin n) K)`,
and `Φ_y(T)` is moved there by `yToFrac`. The Σ∧Σ circuit is exact (not border), over `K(y)`, in
the `n + 1` variables `Option (Fin n)` with `none = z`, transported by
`MvPolynomial.optionEquivLeft`. The factors are nonzero (otherwise `T = 0` and the ratio is
undefined). -/
theorem lemma_5_3 : ∃ C : ℕ, ∀ (K : Type) [Field K] [CharZero K] (n d a : ℕ)
    (ℓ : Fin d → AffineForm K (Fin n)), 1 ≤ a → a ≤ d → (∀ j, (ℓ j).toPoly ≠ 0) →
    let P : Polynomial (MvPolynomial (Fin n) (FractionRing (MvPolynomial (Fin n) K))) :=
      (shift (∏ j, (ℓ j).toPoly)).map (yToFrac (K := K) (σ := Fin n)).toRingHom
    ∃ Q : Polynomial (MvPolynomial (Fin n) (FractionRing (MvPolynomial (Fin n) K))),
      Q.natDegree ≤ d ∧ Polynomial.X ^ (d + 1) ∣ P * Q - Polynomial.derivative^[a] P ∧
      ∃ Φ : SigmaWedgeSigma (FractionRing (MvPolynomial (Fin n) K)) (Option (Fin n)),
        Φ.topFanIn ≤ C * d ^ (3 * a + 1) ∧
        MvPolynomial.optionEquivLeft (FractionRing (MvPolynomial (Fin n) K)) (Fin n) Φ.eval = Q := by sorry

end BorderDiffEq
