-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_claim_2_33
-- name    : AutoQMem.Lindblad.claim_2_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:39.809208+00:00
-- url     : https://prove2.me/theorems/73c239ce-1ddf-4ce0-a733-a4ad2f892c2d
-- title:
--   Claim 2.33: codeword-translation invariance of $G_X(t)$ and of $M(t,0)$
-- statement:
--   Let $\mathcal L(t)$ be a syndrome-based Lindbladian for a CSS code, with induced sector generators $G_X(t)$, $G_Z(t)$. For $w\in C_X$ let $T_w(x)=x\oplus w$. Then for every $h:\Omega_X\to\mathbb R$ and every $t\ge0$,
--   $$G_X(t)(h\circ T_w)=(G_X(t)h)\circ T_w .$$
--   Consequently, if $M$ is the backward transition operator of $G_X$, then for every $a\ge0$ and all $x,y$,
--   $$M(a,0)_{x\oplus w,\,y\oplus w}=M(a,0)_{x,y}:$$
--   the error process $\xi_t=\chi_t\oplus w_0$ has the same backward transition operators, started at $\xi_0=0$, and its law $\Pr[\xi_a=y]=M(a,0)_{w_0,y\oplus w_0}=M(a,0)_{0,y}$ does not depend on the stored codeword $w_0$. The same holds in the Z sector with $C_Z$, $G_Z$ (the paper's exchange $X\leftrightarrow Z$, p. 24).
--
--   The claim is what allows the logical-flip probability of a sector process to be computed from the process started at $0$.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open; W_*(t,0) and M(t,0) are the solutions of (40) and (51) → H(t) and every f_{P,i,α}(t) measurable on [0,∞) and bounded on every [0,T]; W and M are any solutions of (40), (51) in integrated, entrywise form with integrable integrand; reason: the paper's Remark 2.26 regularity; without some regularity the propagator need not exist (rate 1/t), and under it the integral equations have exactly one solution; no continuity or time independence is assumed
--   - encoding: the backward transition operators M^(X)(t, t′) of the error process → any solution M of the integrated equation (51) for G_X, at t′ = 0, compared entrywise at translated arguments; reason: M(t,0)(x, y) is the transition probability from x to y (eq. (50)); the error process is the image of χ under T_{w_0}
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Claim 2.33, eqs. (54)–(55), p. 24 (PDF p. 26); proof Appendix A, p. 64 (PDF p. 66)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_genX
import Definitions.Def_AutoQMem_Lindblad_IsPropagator
open Matrix

namespace AutoQMem.Lindblad

/-- **Claim 2.33 (Codeword-translation invariance).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Claim 2.33, eqs. (54)–(55), p. 24
(PDF 26); proof Appendix A, p. 64 (PDF 66).

For `w ∈ C_X` and `t ≥ 0`, the X-sector generator commutes with the translation
`T_w(x) = x ⊕ w`: `G_X(t)(h ∘ T_w) = (G_X(t) h) ∘ T_w` for every `h : Ω_X → ℝ`. Consequently
the backward transition operator is translation invariant, `M(t, 0)(x ⊕ w, y ⊕ w) = M(t, 0)(x, y)`
for `t ≥ 0`: the error process `ξ_t = χ_t ⊕ w_0` has the same backward transition operators, and
its law `Pr[ξ_t = y] = M(t,0)(w_0, y ⊕ w_0) = M(t,0)(0, y)` does not depend on `w_0`. The Z-sector
statement ("obtained by the exchange X ↔ Z", p. 24) is the second and fourth clause.

**Formalization Note.** `M` is any solution of the integrated Kolmogorov equation (51)
(`IsBackwardPropagator`, Reading R1). -/
theorem claim_2_33 {n mX mZ : ℕ} (C : CSSCode n mX mZ) {ι : Type} [Fintype ι]
    (L : SyndromeLindbladian C ι) :
    (∀ w ∈ C.codeX, ∀ t : ℝ, 0 ≤ t → ∀ h : (Fin n → ZMod 2) → ℝ,
        L.genX t *ᵥ (fun x => h (x + w)) = fun x => (L.genX t *ᵥ h) (x + w)) ∧
    (∀ w ∈ C.codeZ, ∀ t : ℝ, 0 ≤ t → ∀ h : (Fin n → ZMod 2) → ℝ,
        L.genZ t *ᵥ (fun x => h (x + w)) = fun x => (L.genZ t *ᵥ h) (x + w)) ∧
    (∀ M : ℝ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ, IsBackwardPropagator L.genX M →
        ∀ w ∈ C.codeX, ∀ a : ℝ, 0 ≤ a → ∀ x y, M a (x + w) (y + w) = M a x y) ∧
    (∀ M : ℝ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ, IsBackwardPropagator L.genZ M →
        ∀ w ∈ C.codeZ, ∀ a : ℝ, 0 ≤ a → ∀ x y, M a (x + w) (y + w) = M a x y) := by sorry

end AutoQMem.Lindblad
