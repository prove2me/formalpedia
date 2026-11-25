-- Prove2me | Theorems.Thm_DetDLP_trunc_poly_int_contract_and_uniqueness
-- name    : DetDLP.trunc_poly_int_contract_and_uniqueness
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:09.475105+00:00
-- url     : https://prove2.me/theorems/b69617b2-5805-4ecd-9563-0bac4a05f23e
-- title:
--   Truncated-Polynomial Quotient Projection and Canonical Encoding Uniqueness for BTN Contraction
-- statement:
--   For any bipartite multigraph $G = (V, E)$, modulus exponent $P \in \mathbb{N}$, truncation degree $\ell' \in \mathbb{N}$, and local coefficient array $A_{v, t, i} \in [0, 2^P)$ ($v \in V$, $t \in \{0, 1\}^{\delta(v)}$, $0 \le i < \ell'$), let $T_v(t) \in \mathcal{B}_{P, \ell'} = (\mathbb{Z}/2^P\mathbb{Z})[z]/(z^{\ell'})$ denote the truncated polynomial with coefficients $A_{v, t, i} \bmod 2^P$, and let $$Z(z) = \mathrm{Contract}\!\left(G, \,(v, t) \mapsto \sum_{i=0}^{\ell'-1} A_{v, t, i} z^i\right) \in \mathbb{Z}[z]$$ denote the integer-polynomial BTN contraction. Then:
--
--   1. Every local coefficient tuple $(A_{v, t, i})_{i < \ell'}$ canonically encodes $T_v(t) \in \mathcal{B}_{P, \ell'}$;
--   2. The contraction $\mathrm{Contract}(G, T) \in \mathcal{B}_{P, \ell'}$ coincides with the quotient projection of $Z(z)$ modulo $(2^P, z^{\ell'})$;
--   3. Canonical residue encoding in $\mathcal{B}_{P, \ell'}$ is unique: any binary word $w$ encoding $\mathrm{Contract}(G, T)$ equals the binary list encoding of $(([z^i]Z) \bmod 2^P)_{0 \le i < \ell'}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.2 & Section 5.1–5.2 (pp. 7–8, 18–20)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

/-- Algebraic equivalence and canonical encoding uniqueness between integer-polynomial BTN
contraction `BTNContract G (fun v t => ∑ i : Fin ℓ', monomial i (A v t i : ℤ))` and
truncated-polynomial BTN contraction over `TruncPoly P ℓ' = (ℤ / 2^P ℤ)[z] / (z^{ℓ'})`:
1. Each integer coefficient tuple `A v t : Fin ℓ' → ℕ` with `A v t i < 2^P` canonically encodes
   `T v t = truncPolyOfCoeffs P ℓ' (A v t)`.
2. The quotient projection of the integer BTN contraction `Z` equals `BTNContract G T`.
3. Canonical encoding in `TruncPoly P ℓ'` is unique: any word `w` satisfying
   `EncodesTruncPoly P ℓ' w (BTNContract G T)` equals the binary list encoding of the
   canonical mod-`2^P` coefficients of `Z` of degree `< ℓ'`. -/
theorem trunc_poly_int_contract_and_uniqueness :
    ∀ (G : BipartiteMultigraph) (P ℓ' : ℕ)
      (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
      (∀ v t i, A v t i < 2 ^ P) →
      let T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ' :=
        fun v t => truncPolyOfCoeffs P ℓ' (A v t)
      let Z : Polynomial ℤ :=
        BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))
      (∀ v t, EncodesTruncPoly P ℓ' (encodeNatListBin (List.ofFn (A v t))) (T v t)) ∧
      BTNContract G T =
        truncPolyOfCoeffs P ℓ' (fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val)) ∧
      ∀ w : List Bool,
        EncodesTruncPoly P ℓ' w (BTNContract G T) →
        w = encodeNatListBin (List.ofFn fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val)) := by
  sorry

end DetDLP
