-- Prove2me | Theorems.Thm_BenignDegen_Supplement_theorem_6_2
-- name    : BenignDegen.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:31:17.43564+00:00
-- url     : https://prove2.me/theorems/9714f252-ae5e-4555-ae83-25df42336f61
-- title:
--   Theorem 6.2 — fixed-order SC genericity: $\mathcal E_{\mathrm{sc}}$ open in $\mathcal Q$, dense in $\mathcal E$, semialgebraic, $\dim(\mathcal E\setminus\mathcal E_{\mathrm{sc}})<\dim\mathcal E$
-- statement:
--   Fix a sign vector $a\in\{\pm1\}^n$ and an order $1\le d\le n$, and let $u=b_d(a)\in\mathbb R^{N_d}$ be the vector of monomials $(a^T)_{T\in\mathcal I_d}$. Inside the space $\mathcal P_n$ of square-free polynomials consider the **normalized coefficient space**, the **exact cell** and the **strictly complementary cell**
--   $$
--   \begin{aligned}
--   \mathcal Q(a,d)&=\{g\in\mathcal P_{\le 2d}: g(a)=0\},\\
--   \mathcal E(a,d)&=\{g\in\mathcal Q(a,d): \operatorname{argmin}_{X\in\mathcal X_d}\langle C_g,X\rangle=\{uu^\top\}\},\\
--   \mathcal E_{\mathrm{sc}}(a,d)&=\{g\in\mathcal Q(a,d): \exists S\succeq0,\ G_d(S)=g,\ \ker S=\operatorname{span}\{u\}\},
--   \end{aligned}
--   $$
--   where $\mathcal X_d$ is the order-$d$ Boolean moment body, $C_g$ the canonical cost matrix of $g$ and $G_d$ the Gram-to-polynomial map. Then:
--
--   1. $\mathcal E_{\mathrm{sc}}(a,d)$ is open in $\mathcal Q(a,d)$;
--   2. $\mathcal E_{\mathrm{sc}}(a,d)\subseteq\mathcal E(a,d)\subseteq\overline{\mathcal E_{\mathrm{sc}}(a,d)}$, i.e. $\mathcal E_{\mathrm{sc}}(a,d)$ is dense relative to $\mathcal E(a,d)$;
--   3. both $\mathcal E(a,d)$ and $\mathcal E_{\mathrm{sc}}(a,d)$ are semialgebraic subsets of $\mathcal P_n$;
--   4. the exceptional set has strictly smaller dimension:
--   $$
--   \dim\bigl(\mathcal E(a,d)\setminus\mathcal E_{\mathrm{sc}}(a,d)\bigr)<\dim\mathcal E(a,d).
--   $$
--
--   This is the fixed-order half of the genericity argument: among objectives that make $(P_d)$ uniquely rank-one exact at $a$, those that also admit a strictly complementary SOS certificate form a relatively open, dense, full-dimensional piece, and the failures lie in a lower-dimensional semialgebraic set. Theorem 6.3 lifts this to the whole coefficient space.
--
--   **Formalization Note** Square-free polynomials are coefficient functions $\mathrm{Finset}(\mathrm{Fin}\,n)\to\mathbb R$ with the product topology. Semialgebraicity is the published Li–Pong/BCR notion transported along a fixed coordinate bijection with $\mathbb R^{2^n}$, and $\dim A$ is BCR Definition 2.8.1, the Krull dimension of $\mathbb R[X]/I(A)$ with values in $\mathrm{WithBot}\,\mathbb N_\infty$, so $\dim\emptyset=\bot$ and item 4 is meaningful when $\mathcal E\setminus\mathcal E_{\mathrm{sc}}=\emptyset$.
--
--   Differences from the source:
--   - reading: E_sc(a,d) is dense relative to E(a,d) → E_sc(a,d) ⊆ E(a,d) and E(a,d) ⊆ closure E_sc(a,d); reason: relative density presupposes E_sc ⊆ E, which §6 (p.11) states and G.2 (p.31) proves; G.2 (p.32) reads the claim as E_sc ⊆ E ⊆ cl E_sc
--   - encoding: E_sc(a,d) is open in Q(a,d) → E_sc(a,d) = U ∩ Q(a,d) for some open U ⊆ P_n; reason: definition of openness in the subspace topology of Q(a,d) ⊆ P_n
--   - encoding: square-free polynomials g ∈ P_n with the topology of the 2ⁿ-dimensional space → coefficient functions Finset (Fin n) → ℝ with the product topology; reason: linear coordinates of P_n; any linear identification with ℝ^{2ⁿ} gives the same topology
--   - encoding: semialgebraic sets and their dimension [BCR98] → IsSemialgebraicCoeff (image in ℝ^{2ⁿ} under a fixed coordinate bijection is a finite union of basic sets) and semialgDim A = ringKrullDim (ℝ[X]/I(A)) in WithBot ℕ∞; reason: BCR's definition of semialgebraic set and BCR Definition 2.8.1 of dimension, with dim ∅ = ⊥ (BCR's −∞); semialgebraicity is invariant under coordinate permutations
--   - encoding: ker(S) = span{u}, u = b_d(a) → LinearMap.ker (toLin' S) = span ℝ {b_d(a)} on ℝ^{I_d}; reason: kernel of S as a linear map on ℝ^{N_d}; same condition
--   - encoding: a candidate optimizer a ∈ {±1}ⁿ and an order d (§6, under §2's standing 1 ≤ d ≤ n) → a : Fin n → ℤˣ and hypotheses 1 ≤ d, d ≤ n; reason: ℤˣ = {±1} is the base mission's cube encoding; the order range is the standing assumption of §2 (p.4)
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §6, Theorem 6.2, p.11 (proof Appendix G.2, pp.31–32)

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Boolean
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
import Definitions.Def_BenignDegen_Supplement_Semialgebraic
import Definitions.Def_BenignDegen_Supplement_Cells
open SunNLSDP.Equiv Matrix

namespace BenignDegen

namespace Supplement

/-- Theorem 6.2 (fixed-order SC genericity), Kang, *Benign Degeneracy for First-Order Methods in
Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.11 (proof Appendix G.2, pp.31–32).
Fix `a ∈ {±1}ⁿ` and an order `1 ≤ d ≤ n`. Then `E_sc(a,d)` is open in `Q(a,d)` and dense relative
to `E(a,d)`; both cells are semialgebraic; and `dim(E(a,d) \ E_sc(a,d)) < dim E(a,d)`.

**Formalization Note** "Open in `Q(a,d)`" is relative openness: `E_sc = U ∩ Q(a,d)` for an open
`U ⊆ P_n`. "Dense relative to `E(a,d)`" is `E_sc ⊆ E ⊆ cl E_sc` (the paper's reading in G.2; the
inclusion `E_sc ⊆ E` is stated on p.11 and proved in G.2). Topology on `P_n = ℝ^{Finset (Fin n)}`
is the product topology. Semialgebraicity and dimension are those of [BCR98]
(`IsSemialgebraicCoeff`, `semialgDim`). Standing assumption of §2: `1 ≤ d ≤ n`. -/
theorem theorem_6_2 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (a : Fin n → ℤˣ) :
    (∃ U : Set (Finset (Fin n) → ℝ), IsOpen U ∧ EscCell n d a = U ∩ Qcell n d a) ∧
    (EscCell n d a ⊆ Ecell n d a ∧ Ecell n d a ⊆ closure (EscCell n d a)) ∧
    IsSemialgebraicCoeff (Ecell n d a) ∧ IsSemialgebraicCoeff (EscCell n d a) ∧
    semialgDim (Ecell n d a \ EscCell n d a) < semialgDim (Ecell n d a) := by sorry

end Supplement

end BenignDegen
