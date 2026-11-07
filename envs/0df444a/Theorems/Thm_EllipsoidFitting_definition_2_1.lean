-- Prove2me | Theorems.Thm_EllipsoidFitting_definition_2_1
-- name    : EllipsoidFitting.definition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:29.163993+00:00
-- url     : https://prove2.me/theorems/71d536d8-191a-4c79-9069-ab9ab3a37f5a
-- title:
--   Definition 2.1 — $C_F=\frac8{3\pi}$, $\mathbb E[FP_1]=1$, $\{P_j\}$ an orthonormal basis of $L^2(\mu_{\mathrm{sc}})$
-- statement:
--   Let $\mu_{\mathrm{sc}}$ be the semicircle law on $[-2,2]$, $F(x)=\max(2x,0)$ and $P_j(x)=U_j(x/2)$. Then:
--
--   1. $\mu_{\mathrm{sc}}$ is a probability measure;
--   2. $C_F=\mathbb E_{x\sim\mu_{\mathrm{sc}}}[F(x)]=\dfrac8{3\pi}$;
--   3. $\mathbb E_{x\sim\mu_{\mathrm{sc}}}[F(x)P_1(x)]=1$;
--   4. $P_0=1$ and $P_1=x$;
--   5. $\{P_j\}_{j\ge0}$ is an orthonormal basis of $L^2([-2,2],\mu_{\mathrm{sc}})$;
--   6. $F\in L^2(\mu_{\mathrm{sc}})$ and
--   $$
--   F=\sum_{j\ge0}b_jP_j\quad\text{in }L^2(\mu_{\mathrm{sc}}),\qquad b_j=\mathbb E_{x\sim\mu_{\mathrm{sc}}}[F(x)P_j(x)],
--   $$
--   which by 2–4 is the expansion $F(x)=C_F+x+\sum_{j\ge2}b_jP_j(x)$.
--
--   These are the facts the paper's definition asserts; the normalization $\Lambda=\frac1{C_F}F(Q)$ and the variance recursion rest on them.
--
--   **Formalization Note** $L^2(\mu_{\mathrm{sc}})$ is Mathlib's `Lp ℝ 2 muSC`; item 5 is a `HilbertBasis` whose $j$-th vector is a.e. equal to $P_j$; item 6 is a `HasSum` in $L^2$.
--
--   Differences from the source:
--   - encoding: µsc is the semicircle distribution → clause: muSC is a probability measure; reason: a distribution has total mass 1; asserted so the expectations are not taken against a junk measure
--   - encoding: {P_j} is an orthonormal basis for L²([−2,2], µsc) → a HilbertBasis of Lp ℝ 2 µsc whose j-th vector is a.e. P_j; reason: Mathlib's notion of orthonormal basis of a Hilbert space
--   - encoding: We write F(x) = C_F + x + ∑_{j≥2} b_jP_j(x) → F ∈ L² and ∑_{j≥0} b_j P_j = F in L² (HasSum), with b_0 = C_F, b_1 = 1 by the other clauses; reason: the expansion holds in L²(µsc); it is not absolutely convergent pointwise
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Definition 2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_EllipsoidFitting_Fpos

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory Polynomial

/-- **Definition 2.1 (the facts it asserts).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Definition 2.1, p.7:
"Let µsc be the semicircle distribution on [−2, 2] … Then {Pj}j≥0 is an orthonormal basis for
L2([−2, 2], µsc), with P0 = 1 and P1 = x. We write F(x) = CF + x + ∑_{j≥2} bjPj(x), where CF =
Ex∼µsc[F(x)] = 8/(3π), Ex∼µsc[F(x)P1(x)] = 1, and, for j ≥ 2, bj := Ex∼µsc[F(x)Pj(x)]."

1. `µsc` is a probability measure (a "distribution");
2. `C_F = E[F] = 8/(3π)`;
3. `E[F · P_1] = 1`;
4. `P_0 = 1` and `P_1 = x`;
5. there is a Hilbert basis `(e_j)` of `L²(µsc)` whose `j`-th vector is the class of `P_j`
   (so `{P_j}` is an orthonormal basis), and
6. `F ∈ L²(µsc)` and `F = ∑_j b_j P_j` in `L²(µsc)` with `b_j = E[F P_j]` (by 2–4,
   `b_0 = C_F` and `b_1 = 1`, which is the displayed expansion).

**Formalization Note** `L²(µsc)` is `Lp ℝ 2 muSC`; "the class of `P_j`" is
`e_j =ᵐ[µsc] P_j`. The expansion is a `HasSum` in `L²`. -/
theorem definition_2_1 :
    IsProbabilityMeasure muSC ∧
      CF = 8 / (3 * Real.pi) ∧
      ∫ x, Fpos x * (chebP 1).eval x ∂muSC = 1 ∧
      chebP 0 = 1 ∧ chebP 1 = X ∧
      ∃ e : HilbertBasis ℕ ℝ (Lp ℝ 2 muSC),
        (∀ j, (e j : ℝ → ℝ) =ᵐ[muSC] fun x => (chebP j).eval x) ∧
        ∃ f : Lp ℝ 2 muSC, (f : ℝ → ℝ) =ᵐ[muSC] Fpos ∧
          HasSum (fun j => bcoef j • (e j : Lp ℝ 2 muSC)) f := by sorry

end EllipsoidFitting
