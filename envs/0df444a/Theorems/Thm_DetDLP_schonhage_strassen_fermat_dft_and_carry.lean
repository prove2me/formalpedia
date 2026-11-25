-- Prove2me | Theorems.Thm_DetDLP_schonhage_strassen_fermat_dft_and_carry
-- name    : DetDLP.schonhage_strassen_fermat_dft_and_carry
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:01.850068+00:00
-- url     : https://prove2.me/theorems/7ec2f448-6ce6-43a4-8354-245046727805
-- title:
--   Schönhage–Strassen Fermat-Ring DFT Inversion, Carry-Chain Parsimony, and Degree Bounds
-- statement:
--   Proves the four arithmetic and algebraic facts underlying Lemma 2.3 (Two-Layer Schönhage–Strassen Multiplication Gadget, pp. 8–9):
--
--   1. Parameter bounds $L \le J/2$, $L_2^2 \le J$, compiled edge bound $4d + 4J(J+1) < 1100(d+1)$, and maximum degree bound $2\max(L_1,L_2)(J+1) < 136(d+1)^{3/4}$;
--   2. In $\mathcal{R}_J = \mathbb{Z}/(2^J+1)\mathbb{Z}$ with $J = 2^\mu \cdot \mathrm{step}$ and $\omega = 2^{\mathrm{step}}$, we have $2^J = -1$, $\omega^{2^\mu} = -1$, $\omega^{2^{\mu+1}} = 1$, $(-2^{J-\mu})\cdot 2^\mu = 1$, and the two-layer Cooley–Tukey DFT factorization holds;
--   3. Carry-chain equations $c_\ell + \kappa_\ell = z_\ell + B \kappa_{\ell+1}$ ($z_\ell < B$, $\kappa_0 = 0$) uniquely determine every wire $(z_\ell, \kappa_{\ell+1})$ and telescope to $\sum_{\ell<m} c_\ell B^\ell = \sum_{\ell<m} z_\ell B^\ell + \kappa_m B^m$, forcing $\kappa_m = 0$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proof of Lemma 2.3 (pp. 8–9)

import Mathlib

set_option autoImplicit false

namespace DetDLP

/-- Mathematical core of the Two-Layer Schönhage–Strassen Multiplication Gadget (Section 2.3,
Lemma 2.3, pp. 8–9):
(1) Parameter bounds on `J, n_0, L, L_1, L_2` and the compiled edge (`< 1100 (d + 1)`) and
maximum-degree (`< 136 (d + 1)^{3/4}`) bounds;
(2) Fermat-ring `ℤ / (2^J + 1)ℤ` root-of-unity properties (`ω^{2^μ} = -1`, `ω^{2^{μ+1}} = 1`),
explicit inverse `(-2^{J-μ}) · 2^μ = 1`, and the two-layer Cooley–Tukey DFT factorization identity;
(3) Carry-chain parsimony uniqueness (`z_ℓ = (c_ℓ + κ_ℓ) mod B`, `κ_{ℓ+1} = (c_ℓ + κ_ℓ) / B`) and
telescoping identity `∑_{ℓ<m} c_ℓ B^ℓ = ∑_{ℓ<m} z_ℓ B^ℓ + κ_m B^m` forcing `κ_m = 0`. -/
theorem schonhage_strassen_fermat_dft_and_carry :
    (∀ (d J n0 L L1 L2 : ℕ),
       1 ≤ d → 16 ≤ J → 64 * (d + 1) ≤ J ^ 2 → J ^ 2 < 256 * (d + 1) →
       1 ≤ n0 → n0 < J / 16 + 1 → 2 * n0 ≤ L → L < 4 * n0 →
       L1 ≤ L2 → L2 ^ 2 ≤ 2 * L →
       L ≤ J / 2 ∧
       L2 ^ 2 ≤ J ∧
       4 * d + 4 * J * (J + 1) < 1100 * (d + 1) ∧
       (2 * max L1 L2 * (J + 1) : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) ∧
    ((∀ (J μ step : ℕ),
        μ ≤ J → J = 2 ^ μ * step →
        let M := 2 ^ J + 1
        let ω : ZMod M := (2 : ZMod M) ^ step
        (2 : ZMod M) ^ J = -1 ∧
        ω ^ (2 ^ μ) = -1 ∧
        ω ^ (2 ^ (μ + 1)) = 1 ∧
        (-(2 : ZMod M) ^ (J - μ)) * ((2 : ZMod M) ^ μ) = 1) ∧
     (∀ (L1 L2 : ℕ) (ω : ℤ) (x : ℕ → ℤ) (t1 t2 : ℕ),
        ω ^ (L1 * L2) = 1 →
        ∑ j1 ∈ Finset.range L1, ∑ j2 ∈ Finset.range L2,
          x (L2 * j1 + j2) * ω ^ ((L2 * j1 + j2) * (t1 + L1 * t2)) =
        ∑ j2 ∈ Finset.range L2,
          ω ^ (L1 * j2 * t2) *
            (ω ^ (j2 * t1) * ∑ j1 ∈ Finset.range L1, ω ^ (L2 * j1 * t1) * x (L2 * j1 + j2)))) ∧
    (∀ (B m : ℕ) (c z κ : ℕ → ℕ),
       0 < B →
       κ 0 = 0 →
       (∀ ℓ < m, c ℓ + κ ℓ = z ℓ + B * κ (ℓ + 1) ∧ z ℓ < B) →
       (∀ ℓ < m, z ℓ = (c ℓ + κ ℓ) % B ∧ κ (ℓ + 1) = (c ℓ + κ ℓ) / B) ∧
       (∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) =
         (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) + κ m * B ^ m ∧
       ((∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) < B ^ m →
         κ m = 0 ∧ (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) = ∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ)) := by sorry

end DetDLP
