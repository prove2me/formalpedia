-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_3_eqH
-- name    : ApproxGKR.eq_C_3_eqH
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:58.998344+00:00
-- url     : https://prove2.me/theorems/6b8bac65-cbf1-4bfd-a7b2-8f238b19e602
-- title:
--   (C.3) — $\mathrm{eq}_H$, the root-sum formula and the coefficient-norm bounds
-- statement:
--   Let $h\ge1$ and $H=\Omega_h$.
--   1. For all $\rho,z\in\mathbb C$,
--   $$\mathrm{eq}_H(\rho,z)=\sum_{a\in H}L_a(\rho)L_a(z)=\frac1h\Big(1+\sum_{t=1}^{h-1}\rho^tz^{h-t}\Big).$$
--   2. At a label $g\in H^m$, $\mathrm{eq}(\rho,g)=\chi_g(\rho)$ for every $\rho\in\mathbb C^m$.
--   3. Every Lagrange basis polynomial has coefficient norm $\|L_a\|_1=1$.
--   4. If $|f(g)|\le B$ on $H^m$ then $\|\widetilde f\|_1\le h^mB$.
--   5. $|P(z)|\le\|P\|_1$ whenever every coordinate of $z$ has modulus at most one.
--   6. If every coordinate of $\rho_0,\rho_1$ and both coefficients $c_0,c_1$ have modulus at most one, then $\|\Psi\|_1\le2$ for $\Psi=c_0\,\mathrm{eq}(\rho_0,\cdot)+c_1\,\mathrm{eq}(\rho_1,\cdot)$.
--   7. For every polynomial $p$ of degree at most $D$,
--   $$\sum_{a\in H}p(a)=h\sum_{0\le t\le D,\ h\mid t}[X^t]p(X).$$
--
--   Item 7 is how the verifier sums a round polynomial over $H$; items 3–6 bound every quantity the protocol handles on the unit torus.
--
--   Differences from the source:
--   - generalization: h a power of two ≥ 2 → any h ≥ 1; reason: the identities hold for every h ≥ 1
--   - generalization: Ψ_i with coefficients (1, 0) or (1, λ), |λ| = 1 → any coefficients of modulus at most one; reason: the page's coefficients are among them
--   - generalization: ‖Ṽ_i‖₁ ≤ h^{m_i}B_V for the gate values → ‖f̃‖₁ ≤ h^m B for any f bounded by B; reason: specializes to f = V_i, B = B_V
--   - generalization: the root-sum formula for the round polynomials p_j → for every polynomial of degree at most D; reason: p_j has degree at most D
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), eq. (C.3), p.31; §C.1, p.32; step 1, p.33

import Mathlib
import Definitions.Def_ApproxGKR_mvNorm1
import Definitions.Def_ApproxGKR_lagrangeBasis

namespace ApproxGKR

/-- **Equation (C.3), the root-sum formula and the coefficient-norm bounds** (pp.31–33).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), eq. (C.3), p.31; §C.1, p.32; step 1, p.33.
1. `eq_H(ρ, z) = Σ_{a∈H} L_a(ρ)L_a(z) = (1/h)(1 + Σ_{t=1}^{h−1} ρ^t z^{h−t})` for all `ρ, z ∈ ℂ`;
2. at a label `g ∈ H^m`, `eq(ρ, g) = χ_g(ρ)`;
3. every Lagrange basis polynomial has coefficient norm one;
4. `‖Ṽ‖₁ ≤ h^m B` whenever every value `f(g)` has modulus at most `B`;
5. `|f(z)| ≤ ‖f‖₁` whenever every coordinate of `z` has modulus at most one;
6. `‖Ψ‖₁ ≤ 2` when every coordinate of `ρ₀, ρ₁` and both coefficients have modulus at most one;
7. `Σ_{a∈H} p(a) = h Σ_{0≤t≤D, h|t} [X^t]p(X)` for every polynomial `p` of degree at most `D`.

**Formalization Note** Stated for every `h ≥ 1` (the page fixes a power of two `h ≥ 2`) and,
in item 6, for coefficients of modulus at most one (the page's coefficients are `(1, 0)` and
`(1, λ)` with `|λ| = 1`). -/
theorem eq_C_3_eqH (h : ℕ) (hh : 1 ≤ h) :
    (∀ ρ z : ℂ, eqH h ρ z = (h : ℂ)⁻¹ * (1 + ∑ t ∈ Finset.Ico 1 h, ρ ^ t * z ^ (h - t))) ∧
    (∀ (m : ℕ) (ρ : Fin m → ℂ) (g : Fin m → Fin h),
      MvPolynomial.eval (labelPoint g) (eqMv h ρ) = MvPolynomial.eval ρ (chi g)) ∧
    (∀ a : Fin h, polyNorm1 (lagrangeBasis h a) = 1) ∧
    (∀ (m : ℕ) (f : (Fin m → Fin h) → ℂ) (B : ℝ), (∀ g, ‖f g‖ ≤ B) →
      mvNorm1 (extension f) ≤ (h : ℝ) ^ m * B) ∧
    (∀ (m : ℕ) (P : MvPolynomial (Fin m) ℂ) (z : Fin m → ℂ), (∀ j, ‖z j‖ ≤ 1) →
      ‖MvPolynomial.eval z P‖ ≤ mvNorm1 P) ∧
    (∀ (m : ℕ) (ρ0 ρ1 : Fin m → ℂ) (c0 c1 : ℂ), (∀ j, ‖ρ0 j‖ ≤ 1) → (∀ j, ‖ρ1 j‖ ≤ 1) →
      ‖c0‖ ≤ 1 → ‖c1‖ ≤ 1 → mvNorm1 (Psi h ρ0 ρ1 c0 c1) ≤ 2) ∧
    (∀ (p : Polynomial ℂ) (D : ℕ), p.natDegree ≤ D →
      ∑ a : Fin h, p.eval (root h a.val) =
        (h : ℂ) * ∑ t ∈ (Finset.range (D + 1)).filter (fun t => h ∣ t), p.coeff t) := by sorry

end ApproxGKR
