-- Prove2me | Theorems.Thm_BorderDiffEq_proposition_5_4
-- name    : BorderDiffEq.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:55.619589+00:00
-- url     : https://prove2.me/theorems/48a40beb-7a3c-4911-b02c-bc2bd75ffd8d
-- title:
--   Proposition 5.4 — truncated differential equation $\sum_jb_jD^jF\equiv0\pmod{z^{d+1}}$ with small coefficients
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $F$ be a field of characteristic zero and
--   $$
--   f_\varepsilon=\sum_{i=1}^{k}T_i=f+O(\varepsilon),\qquad T_i=\prod_{a=1}^{d_i}\ell_{ia},\quad d_i\le d,
--   $$
--   where $f\in F[x]$ is nonzero, every $T_i$ is nonzero and the $\ell_{ia}$ are affine linear with coefficients in $F((\varepsilon))$. Let $F(y,z,x):=f(y+zx)$. Then there are $1\le r\le\min\{k,d+1\}$ and $b_0,\dots,b_r\in F(y)[z,x]$ with $\deg_zb_j\le d$, such that
--   $$
--   \sum_{j=0}^rb_j\,D^jF\equiv0\pmod{z^{d+1}}\quad(24),\qquad b_r(y,0,x)\neq0\quad(25).
--   $$
--   Moreover:
--
--   1. viewed as a polynomial in $(z,x)$ over $F(y)$, each $b_j$ lies in the border $\overline{\Sigma\wedge\Sigma}$ with top fan-in at most $(kd+1)^{Ck^2}$ and formal degree at most $C(d+k^2)$;
--   2. there is a nonzero product $H(y)$ of at most $kd$ affine linear polynomials over $F$ and polynomials $p_j\in F[y,x]$ with $\deg_yp_j\le kd$ and $\deg_xp_j\le Ck^2$, such that $p_j=H(y)\,\beta_j$ for $\beta_j(y,x):=b_j(y,0,x)$, and
--   $$
--   H(y+zx)\,b_j(y,z,x)\equiv p_j(y+zx,x)\pmod{z^{d+1}},\qquad\text{i.e.}\quad b_j=\Big[\frac{p_j(y+zx,x)}{H(y+zx)}\Big]_{\le d}\quad(28).
--   $$
--   The proof of Theorem 2.1 solves (24) for the $z$-coefficients of $F$ and uses part 2 to choose a point $y=\alpha$ where all denominators survive.
--
--   **Formalization Note** $F(y)$ is `FractionRing (MvPolynomial (Fin n) F)`; $b_j$ is a polynomial in $z$ over `MvPolynomial (Fin n) F(y)`, and $b_j(y,0,x)$ is its `coeff 0`. The sum is a $\Sigma\Pi\Sigma$ circuit over $F((\varepsilon))$ with at most $k$ product gates of fan-in at most $d$. $\deg_y$ and $\deg_x$ are total degrees in each block of variables. The border circuit of part 1 is over $F(y)$ in the variables `Option (Fin n)` (`none` $=z$).
--
--   Differences from the source:
--   - generalization: constants in $F(\varepsilon)$ → constants in $F((\varepsilon))$ (`LaurentSeries F`); reason: $F(\varepsilon)\subset F((\varepsilon))$ and $\mathrm{val}_\varepsilon$, $\lim_{\varepsilon\to0}\varepsilon^{-m}$ restrict to the paper's; the source's instances are instances of the Lean statement
--   - generalization: $f_\varepsilon=f+O(\varepsilon)$ for $\ell_{ia}\in F(\varepsilon)[x]$ → $f_\varepsilon=f+\varepsilon S$ with $S\in F[[\varepsilon]][x]$; reason: for $F(\varepsilon)$ constants this is the same condition
--   - generalization: exactly $k$ summands → a circuit with at most $k$ product gates; reason: fewer summands $k'\le k$ is the source's statement for $k'$, and every bound is monotone in $k$
--   - reading: $(kd)^{O(k^2)}$, $O(d+k^2)$, $O(k^2)$ → $(kd+1)^{Ck^2}$, $C(d+k^2)$, $Ck^2$ with one absolute $C$ before the field and all parameters; reason: $O(\cdot)$ as an absolute constant; the $+1$ keeps $(kd)^{O(k^2)}$ meaningful at $kd\le1$
--   - encoding: (28): $b_j=[p_j(y+zx,x)/H(y+zx)]_{\le d}=[\beta_j(y+zx,x)]_{\le d}$ → $H(y+zx)b_j\equiv p_j(y+zx,x)\pmod{z^{d+1}}$ and $p_j=H\beta_j$ in $F(y)[x]$; reason: with $\deg_zb_j\le d$ these are equivalent, since $H(y+zx)$ equals $H(y)\ne0$ at $z=0$; the second form follows from $p_j=H\beta_j$
--   - encoding: "In particular, all $b_j(\alpha,z,x)$ are defined whenever $H(\alpha)\ne0$, and $b_r(\alpha,0,x)\ne0\iff p_r(\alpha,x)\ne0$" → not a separate conjunct; reason: it is a consequence of $p_r=H\beta_r$ and (28), both stated
--   - encoding: part 1's border $\overline{\Sigma\wedge\Sigma}$ over $F(y)$: constants in $F(y)(\varepsilon)$, $b_j+\varepsilon g$ with $g\in F(y)[\varepsilon][z,x]$ → `InBorderSWS` over $F(y)$: constants in $F(y)((\varepsilon))$, $b_j+\varepsilon S$ with $S\in F(y)[[\varepsilon]][z,x]$; reason: the two classes coincide: truncating the finitely many Laurent-series constants of a $\Sigma\wedge\Sigma$ circuit at a high enough order changes its output only by terms of positive $\varepsilon$-valuation (the exponents are finite), which gives constants in $F(y)[\varepsilon,\varepsilon^{-1}]$ with the same top fan-in and exponents
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Proposition 5.4, pp.34–35 (proof pp.35–37)

import Mathlib
import Definitions.Def_BorderDiffEq_AffineForm
import Definitions.Def_BorderDiffEq_SPS
import Definitions.Def_BorderDiffEq_IsEpsApprox
import Definitions.Def_BorderDiffEq_InBorderSWS
import Definitions.Def_BorderDiffEq_shift
import Definitions.Def_BorderDiffEq_diagSubst
import Definitions.Def_BorderDiffEq_yToFrac

namespace BorderDiffEq

/-- **Proposition 5.4 (truncated differential equation)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Proposition 5.4, pp.34–35). Let `F` be a field of characteristic zero and
`f_ε = ∑_{i=1}^k Tᵢ = f + O(ε)`, `Tᵢ = ∏_{a=1}^{dᵢ} ℓᵢₐ`, `dᵢ ≤ d`, with `f ≠ 0`, every `Tᵢ ≠ 0` and
`ℓᵢₐ ∈ F(ε)[x]` affine linear. Let `F(y, z, x) := f(y + z x)`. There exist
`1 ≤ r ≤ min{k, d+1}` and `b₀, …, b_r ∈ F(y)[z, x]` with `deg_z bⱼ ≤ d`, such that
`∑ⱼ bⱼ D^j F ≡ 0 (mod z^{d+1})` (24) and `b_r(y, 0, x) ≠ 0` (25). Moreover:
1. viewed as polynomials in `(z, x)` over `F(y)`, each `bⱼ` has a border `cl(Σ∧Σ)` circuit of top
fan-in `(kd)^{O(k²)}` and formal degree `O(d + k²)`;
2. there is a nonzero product `H(y)` of at most `kd` affine linear polynomials such that
`βⱼ(y, x) := bⱼ(y, 0, x)` and `pⱼ := H(y) βⱼ` satisfy `pⱼ ∈ F[y, x]`, `deg_y pⱼ ≤ kd`,
`deg_x pⱼ = O(k²)`, and `bⱼ = [pⱼ(y + z x, x) / H(y + z x)]_{≤d}` (28).

**Formalization Note.** One absolute constant `C`, before the field and every parameter, reads every
`O(·)`: `(kd)^{O(k²)}` is `(k d + 1)^{C k²}`, `O(d + k²)` is `C (d + k²)`, `O(k²)` is `C k²`.
`F(ε)` is generalized to `F((ε))`; `f + O(ε)` is `IsEpsApprox`; the sum is a ΣΠΣ circuit over
`F((ε))` with at most `k` products of fan-in at most `d`. `F(y) = FractionRing (MvPolynomial (Fin n) F)`;
`bⱼ` is a polynomial in `z` over `MvPolynomial (Fin n) F(y)` (the `x`-variables), `D` is
`Polynomial.derivative`, "mod `z^{d+1}`" is divisibility by `X ^ (d+1)`, `bⱼ(y, 0, x)` is
`coeff 0`. Part 1's circuit is in the border class (overlined on p.34) over `F(y)` in the variables
`Option (Fin n)` (`none = z`), via `MvPolynomial.optionEquivLeft`. In part 2, `pⱼ` is a polynomial in
`(y, x)` (`Sum.inl`, `Sum.inr`); `deg_y`, `deg_x` are total degrees in each block; `pⱼ = H βⱼ` is
stated in `F(y)[x]`; and (28) is stated in polynomial form,
`H(y + z x) · bⱼ ≡ pⱼ(y + z x, x) (mod z^{d+1})`, which with `deg_z bⱼ ≤ d` is equivalent to the
truncated quotient because `H(y + z x)` is `H(y) ≠ 0` at `z = 0`. Its second form
`[βⱼ(y + z x, x)]_{≤d}` and the closing "In particular" sentence follow from these clauses and are
not separate conjuncts. -/
theorem proposition_5_4 : ∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k d : ℕ)
    (f : MvPolynomial (Fin n) F) (Φ : SPS (LaurentSeries F) (Fin n)),
    f ≠ 0 → Φ.topFanIn ≤ k → (∀ i, Φ.deg i ≤ d) → (∀ i, ∏ a, (Φ.form i a).toPoly ≠ 0) →
    IsEpsApprox Φ.eval f →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ min k (d + 1) ∧
    ∃ b : Fin (r + 1) → Polynomial (MvPolynomial (Fin n) (FractionRing (MvPolynomial (Fin n) F))),
      (∀ j, (b j).natDegree ≤ d) ∧
      -- (24)
      Polynomial.X ^ (d + 1) ∣ ∑ j : Fin (r + 1), b j * Polynomial.derivative^[(j : ℕ)]
        ((shift f).map (yToFrac (K := F) (σ := Fin n)).toRingHom) ∧
      -- (25)
      (b (Fin.last r)).coeff 0 ≠ 0 ∧
      -- part 1
      (∀ j, InBorderSWS (FractionRing (MvPolynomial (Fin n) F)) (Option (Fin n))
        ((k * d + 1) ^ (C * k ^ 2)) ((C * (d + k ^ 2) : ℕ) : ℕ∞)
        ((MvPolynomial.optionEquivLeft (FractionRing (MvPolynomial (Fin n) F)) (Fin n)).symm (b j))) ∧
      -- part 2
      ∃ (mH : ℕ) (L : Fin mH → AffineForm F (Fin n)), mH ≤ k * d ∧
        (∏ i, (L i).toPoly) ≠ 0 ∧
        ∃ p : Fin (r + 1) → MvPolynomial (Fin n ⊕ Fin n) F,
          (∀ j, ∀ μ ∈ (p j).support,
            ∑ l, μ (Sum.inl l) ≤ k * d ∧ ∑ l, μ (Sum.inr l) ≤ C * k ^ 2) ∧
          (∀ j, yToFrac (p j) =
            yToFrac (MvPolynomial.rename Sum.inl (∏ i, (L i).toPoly)) * (b j).coeff 0) ∧
          (∀ j, Polynomial.X ^ (d + 1) ∣
            (shift (∏ i, (L i).toPoly)).map (yToFrac (K := F) (σ := Fin n)).toRingHom * b j -
              (diagSubst (Polynomial.C (p j))).map (yToFrac (K := F) (σ := Fin n)).toRingHom) := by sorry

end BorderDiffEq
