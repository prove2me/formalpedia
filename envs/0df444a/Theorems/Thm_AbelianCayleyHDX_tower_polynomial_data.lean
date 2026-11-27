-- Prove2me | Theorems.Thm_AbelianCayleyHDX_tower_polynomial_data
-- name    : AbelianCayleyHDX.tower_polynomial_data
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:27:09.265618+00:00
-- url     : https://prove2.me/theorems/420d72e6-e038-48b4-96ad-530fb4127d29
-- title:
--   Evaluation data from the Garcia–Stichtenoth tower, with polynomial independence of minors (Lemma 4.1, Prop. 4.6)
-- statement:
--   Fix $q=2^h\ge8$ and a field $F$ with $q^2$ elements. Take a level of the Garcia–Stichtenoth tower (Lemma 4.1) with genus $g\ge4$ and at least $(q-2)g$ rational points away from $P_\infty$, and set up the data of Sections 4.1–4.2. Concretely: $\nu=(q-2)g$ selected points $P_a$; the space $W=L(3gP_\infty)$, so that $t=\dim W=2g+1$, with $W^\vee\cong F^t$; the evaluation vectors $e_{P_a}\in F^t$; and, for $k=\lfloor g/4\rfloor$ and $m=3k$, the $k\times m$ matrix of linear forms $L_{ij}(x)=x(u_iz_j)$. Then:
--
--   1. the vectors $e_{P_a}$ span $F^t$, are nonzero, and are pairwise non-proportional;
--   2. every nonzero linear functional on $F^t$ vanishes at no more than $3g$ of them;
--   3. at every selected point the matrix has rank one: $L_{ij}(e_P)=u_i(P)z_j(P)$;
--   4. the $\binom mk$ maximal minors $\det\big(L_{ij}\big)_{i\le k,\ j\in J}$ are linearly independent **as polynomials** in the coordinates of $F^t$;
--   5. the vectors $e_{P_a}$ are computable in time polynomial in $t$.
--
--   In clause 4 each $L_{ij}$ is the linear polynomial $\sum_r L_{ij}(e_r)X_r$. This is the first paragraph of the proof of Proposition 4.6, "Polynomial independence": the matrix is 1-generic, so its maximal minors form a minimal generating set of their ideal [Eis05, Theorem 6.4 and Corollary A2.61].
--
--   In the formal statement, for every $g_0$ there is a sequence of genera $g_j\to\infty$, all at least $g_0$, carrying such data, and for every binary encoding of $F$ one Turing machine lists the vectors $e_{P_a}$ in time polynomial in $t_j$.
--
--   The second paragraph of Proposition 4.6 upgrades clause 4 to linear independence as functions $F^t\to F$, using clause 3 at a basis of evaluation points. That step is proved, so this statement implies `tower_evaluation_data`.
--
--   **Formalization Note** The curves, the tower and the Riemann–Roch spaces are not formalized; only their consequences in coordinates are stated. Polynomials are `MvPolynomial (Fin t) F`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 4.1 and Section 4.1 (p.15), Section 4.2 (p.16), Proposition 4.6 first paragraph 'Polynomial independence' (p.17); Eisenbud, The Geometry of Syzygies, Thm 6.4 and Cor. A2.61; Garcia–Stichtenoth (1996); Guruswami–Xing (2022)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

/-- **Section 4.1–4.2 and Proposition 4.6 (polynomial form): evaluation data from the Garcia–Stichtenoth tower**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937
(held version, sha256 6f5b0daa…75ba), Lemma 4.1, the construction of Section 4.1 (p.15), the matrix
of linear forms of Section 4.2 (p.16) and Proposition 4.6 (p.17)). Fix `q = 2^h ≥ 8` and `F = 𝔽_{q²}`.
At a level of the Garcia–Stichtenoth tower of genus `g ≥ 4` with `|P_r| ≥ (q − 2)g`, choose
`ν = (q − 2)g` rational points `P_1, …, P_ν`, put `G = 3gP_∞`, `W = L(G)`, `t = dim W = 2g + 1`, and
identify `W^∨ ≅ F^t`; let `e_P ∈ W^∨` be evaluation at `P`. With `k = ⌊g/4⌋`, `m = 3k`, bases
`u_1, …, u_k` of `U ≤ L((g + k)P_∞)` and `z_1, …, z_m` of `V ≤ L(G − (g + k)P_∞)`, let
`L_{ij}(x) = x(u_i z_j)` for `x ∈ W^∨`. The paper shows:
1. the `e_P` span `W^∨`, are nonzero and pairwise non-proportional (p.15);
2. every nonzero `s ∈ W` (a nonzero functional on `W^∨`) vanishes at no more than `3g` of the
   selected points (p.15);
3. `L_{ij}(e_P) = u_i(P) z_j(P)` (rank one at every selected point; Eq. (4.1));
4. the `k × k` minors `det (L_{ij})_{i, j ∈ J}`, as polynomials in the `t` coordinates of `F^t`
   (each `L_{ij}` written as the linear polynomial `∑_r L_{ij}(e_r) X_r`), are linearly independent
   over `F` (Proposition 4.6, first paragraph "Polynomial independence", via 1-genericity and
   [Eis05, Theorem 6.4, Corollary A2.61]);
5. the points (as vectors of `F^t`) are computable in time polynomial in `t` ([GX22], p.15).

Stated as: for every `g₀` there is a sequence of genera `g_j → ∞`, all `≥ g₀`, with vectors
`e_j : Fin ((q − 2) g_j) → F^{2g_j + 1}` and linear forms `L_j` with these properties, and for every
encoding `enc` of `F` one machine outputs `t_j = 2g_j + 1` and the list of the `e_j(a)` within
time polynomial in `t_j`.

**Formalization Note** The curve, the tower and the Riemann–Roch spaces are not formalized; this
statement records their consequences used in Section 4.3 in coordinates. "For every `g₀`" reflects
"discarding finitely many earlier tower levels" (p.17). -/
theorem tower_polynomial_data (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hF : Fintype.card F = (2 ^ h) ^ 2) (g₀ : ℕ) :
    ∃ g : ℕ → ℕ, Tendsto g atTop atTop ∧ (∀ j, g₀ ≤ g j) ∧
    ∃ (e : ∀ j, Fin ((2 ^ h - 2) * g j) → (Fin (2 * g j + 1) → F))
      (L : ∀ j, Fin (g j / 4) → Fin (3 * (g j / 4)) → Module.Dual F (Fin (2 * g j + 1) → F)),
      (∀ j,
        Submodule.span F (Set.range (e j)) = ⊤ ∧
        (∀ a, e j a ≠ 0) ∧
        (∀ a b, a ≠ b → ∀ c : F, e j a ≠ c • e j b) ∧
        (∀ c : Module.Dual F (Fin (2 * g j + 1) → F), c ≠ 0 →
          (Finset.univ.filter fun a => c (e j a) = 0).card ≤ 3 * g j) ∧
        (∀ a, ∃ (u : Fin (g j / 4) → F) (z : Fin (3 * (g j / 4)) → F),
          ∀ i l, L j i l (e j a) = u i * z l) ∧
        LinearIndependent F (fun J : {J : Finset (Fin (3 * (g j / 4))) // J.card = g j / 4} =>
          (Matrix.of fun i l => ∑ r : Fin (2 * g j + 1),
            MvPolynomial.C (L j i (J.1.orderEmbOfFin J.2 l) (Pi.single r 1)) *
              MvPolynomial.X r).det)) ∧
      ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin M (encNat j)
            (encNat (2 * g j + 1) ++ encList (encFVec enc) (List.ofFn (e j)))
            (p.eval (2 * g j + 1)) := by sorry

end AbelianCayleyHDX
