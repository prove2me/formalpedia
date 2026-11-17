-- Prove2me | Theorems.Thm_EntangledPIR_Supplement_theorem_3_1_ii
-- name    : EntangledPIR.Supplement.theorem_3_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:27:41.396901+00:00
-- url     : https://prove2.me/theorems/3cb38207-37d5-4ed4-8b98-11b227bea519
-- title:
--   Theorem 3.1(ii) — cut-and-choose lower bound $D(\zeta_x,\zeta_{x'})=\frac12\ell^{-\mathrm{wt}(\gamma)/2}|\hat\mu_x(\gamma)-\hat\mu_{x'}(\gamma)|$
-- statement:
--   This is the lower-bound half of the cut-and-choose theorem against coherent attacks: the exponent $\mathrm{wt}(\gamma)/2$ of part (i) cannot be improved.
--
--   Let $k,d\ge1$ and $\ell\ge2$ be integers. Copy $(i,j)\in[k]\times[\ell]$ is a register $B_{i,j}$ containing a register $P'_{i,j}$ of $d$ qubits, and its test is a projector $\Pi_{i,j}$ on $B_{i,j}$ satisfying (3.1),
--   $$\Pi_{i,j}\,|J\rangle\langle J|_{P'_{i,j}}\,\Pi_{i,j}=2^{-d}\,\Pi_{i,j}\qquad(J\in\{0,1\}^d).$$
--   Let $X$ be a finite set of secrets and, for each $x\in X$, let $\mu_x$ be a distribution of the shares $y=(y_1,\dots,y_k)\in(\{0,1\}^d)^k$. For a register $R$ and a state $\rho$ of $RB$, $\zeta_x=R_x(A(\rho))$ is the subnormalized state, on acceptance of the procedure (random untested positions $t$, tests of all other copies, measurement of the untested copies and one-time padding of the shares), of $R$ and the classical registers holding $t$ and $K$. $D$ is the trace distance $\frac12\|\cdot\|_1$.
--
--   For $\gamma=(\gamma_1,\dots,\gamma_k)\in(\{0,1\}^d)^k$ write
--   $$\hat\mu_x(\gamma)=\mathbb E_{y\sim\mu_x}(-1)^{\gamma\cdot y},\qquad \gamma\cdot y=\gamma_1\cdot y_1+\dots+\gamma_k\cdot y_k \bmod 2,$$
--   and let $\mathrm{wt}(\gamma)$ be the number of indices $i$ with $\gamma_i\ne0^d$.
--
--   **Theorem.** If $\Pi_{i,j}\ne0$ for every copy, then for every nonzero $\gamma$ there are a register $R$ and a state $\rho$ of $RB$ with $\operatorname{Tr}\rho=1$ such that, for all $x,x'\in X$,
--   $$D(\zeta_x,\zeta_{x'})=\tfrac12\,\ell^{-\mathrm{wt}(\gamma)/2}\,\bigl|\hat\mu_x(\gamma)-\hat\mu_{x'}(\gamma)\bigr|.$$
--
--   The register and the state depend only on $\gamma$, not on the secrets. For a sharing with privacy threshold $\lambda$ and a $\gamma$ of weight $\lambda+1$ that separates two secrets, this matches the upper bound $\ell^{-(\lambda+1)/2}/(1-\ell^{-1/2})$ of part (i) up to a constant factor, which yields Corollary 3.2.
--
--   **Formalization Note** The setting is exactly that of the published part (i), `EntangledPIR.theorem_3_1_i`, and uses the published definitions `IsTestFamily`, `IsShareDistribution`, `Amap`, `Rmap` and `DimFreeShadow.traceDistance`. The copy register is $P'_{i,j}\otimes E_{i,j}$ with an arbitrary finite remainder $E_{i,j}$. The register $R$ is an existential finite type, and $\rho$ is positive semidefinite with trace exactly $1$. The inner product $\gamma_i\cdot y_i$ is the integer `bdot`, and $(-1)$ raised to the integer sum equals $(-1)^{\gamma\cdot y}$.
--
--   Differences from the source:
--   - encoding: a register R (of qubits) → an existential finite type R with its Fintype and DecidableEq instances; reason: registers are finite-dimensional, and a finite type indexes the computational basis of any finite-dimensional register
--   - encoding: γ·y = γ_1·y_1 + ⋯ + γ_k·y_k modulo two in the exponent of −1 → the integer sum ∑_i bdot (γ i) (y i); reason: (−1)^n depends only on n mod 2, so the coefficient is the same number
--   - encoding: copy (i, j) is a register B_{i,j} that contains the d-qubit register P′_{i,j} → B_{i,j} = Bits d × E_{i,j} for an arbitrary finite E_{i,j} (published CopyB); reason: the published convention of part (i); a finite-dimensional register containing P′ as a tensor factor is P′ ⊗ E
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026), sha256 5cfce27c325365d29c042cf08ea41ddd83b9a5c0f711ef85e2620d8955251384, Theorem 3.1(ii), p.13 (PDF p.15); setting §3, p.12 (PDF p.14), Equation (3.1), p.12; ζ_x via (3.4)–(3.5), pp.15–16

import Definitions.Def_EntangledPIR_CutChoose
import Definitions.Def_DimFreeShadow_traceDistance

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

namespace Supplement

/-- **Theorem 3.1(ii) (Cut-and-Choose against Coherent Attacks, lower bound)**, Mantri, *Private
Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), p.13 (PDF p.15).

Suppose that (3.1) holds. If `Π_{i,j} ≠ 0` for every copy, then for every nonzero
`γ = (γ_1, …, γ_k) ∈ ({0,1}^d)^k` there are a register `R` and a state `ρ` of `RB` with `Tr ρ = 1`
such that, for all secrets `x, x′ ∈ X`,
`D(ζ_x, ζ_{x′}) = ½ ℓ^{-wt(γ)/2} |µ̂_x(γ) − µ̂_{x′}(γ)|`, where `µ̂_x(γ) = E_{y∼µ_x} (−1)^{γ·y}`,
`wt(γ)` is the number of nonzero coordinates `γ_i`, and `γ·y = γ_1·y_1 + ⋯ + γ_k·y_k` mod 2.

**Formalization Note** The setting is the one of the published part (i), `EntangledPIR.theorem_3_1_i`:
`1 ≤ k`, `1 ≤ d`, `2 ≤ ℓ` (p.12), copies `B_{i,j} = P′_{i,j} ⊗ E_{i,j}` with arbitrary finite
remainders `E_{i,j}`, tests satisfying `IsTestFamily` (projectors with (3.1)), share distributions
`IsShareDistribution`, the state on acceptance `ζ_x = R_x(A(ρ))` (`Rmap (mu x) (Amap Pi ρ)`) and
`D` = `DimFreeShadow.traceDistance` (`½‖·‖₁`). The register `R` is existential, chosen after `γ`
and before `x, x′`, as a finite type; `ρ` is positive semidefinite with trace exactly one. The
Fourier coefficient is `∑_y µ_x(y) (−1)^{∑_i γ_i·y_i}`, with `γ_i·y_i` the integer `EntangledPIR.bdot`;
`(−1)` to an integer only depends on its parity, so this is the paper's exponent mod 2. `wt(γ)`
counts the blocks `γ_i ≠ 0^d`, not the bits. The power `ℓ^{-wt(γ)/2}` is the real power. -/
theorem theorem_3_1_ii {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ)
    {E : Fin k × Fin ℓ → Type} [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hPi : IsTestFamily Pi)
    (hPi0 : ∀ c, Pi c ≠ 0)
    {X : Type} [Fintype X] (mu : X → ShareVec k d → ℝ) (hmu : IsShareDistribution mu)
    (γ : ShareVec k d) (hγ : γ ≠ fun _ => bzero d) :
    ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R)
      (ρ : Matrix (R × AllB d E) (R × AllB d E) ℂ),
      ρ.PosSemidef ∧ ρ.trace = 1 ∧
        ∀ x x' : X,
          DimFreeShadow.traceDistance (Rmap (R := R) (mu x) (Amap Pi ρ))
              (Rmap (R := R) (mu x') (Amap Pi ρ)) =
            1 / 2 * (ℓ : ℝ) ^ (-((Finset.univ.filter (fun i => γ i ≠ bzero d)).card : ℝ) / 2) *
              |(∑ y : ShareVec k d, mu x y * (-1 : ℝ) ^ (∑ i, bdot (γ i) (y i))) -
                (∑ y : ShareVec k d, mu x' y * (-1 : ℝ) ^ (∑ i, bdot (γ i) (y i)))| := by sorry

end Supplement

end EntangledPIR
