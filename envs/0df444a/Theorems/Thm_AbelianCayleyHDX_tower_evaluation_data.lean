-- Prove2me | Theorems.Thm_AbelianCayleyHDX_tower_evaluation_data
-- name    : AbelianCayleyHDX.tower_evaluation_data
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T23:42:40.16618+00:00
-- url     : https://prove2.me/theorems/44355182-cc93-47af-bc4f-080b69a31122
-- title:
--   Evaluation data from the Garcia–Stichtenoth tower (Lemma 4.1, Section 4.1–4.2, Proposition 4.6)
-- statement:
--   Fix $q=2^h\ge8$ and a field $F$ with $q^2$ elements. Take a level of the Garcia–Stichtenoth tower (Lemma 4.1) with genus $g\ge4$ and at least $(q-2)g$ rational points $\mathcal P_r$ away from $P_\infty$. Choose $\nu=(q-2)g$ of these points, $P_1,\dots,P_\nu$, put $G=3gP_\infty$ and $W=L(G)$, so that $t=\dim_F W=2g+1$, and identify $W^\vee\cong F^t$. Let $e_P\in W^\vee$ be evaluation at $P$. Set $k=\lfloor g/4\rfloor$ and $m=3k$, choose bases $u_1,\dots,u_k$ of $U\le L((g+k)P_\infty)$ and $z_1,\dots,z_m$ of $V\le L(G-(g+k)P_\infty)$, and let $L_{ij}(x)=x(u_iz_j)$ for $x\in W^\vee$. Then:
--
--   1. the vectors $e_{P_1},\dots,e_{P_\nu}$ span $F^t$, are nonzero, and are pairwise non-proportional;
--   2. every nonzero linear functional on $F^t$, that is, every nonzero $s\in W$, vanishes at no more than $3g$ of the $e_{P_a}$;
--   3. at every selected point the matrix of linear forms has rank one: $L_{ij}(e_P)=u_i(P)\,z_j(P)$ (Eq. (4.1));
--   4. the $\binom{m}{k}$ maximal minors $p_J(x)=\det\big(L_{ij}(x)\big)_{i\le k,\ j\in J}$ are linearly independent as functions $F^t\to F$ (Proposition 4.6);
--   5. the vectors $e_{P_a}$ can be computed in time polynomial in $t$ ([GX22]).
--
--   In the formal statement, for every $g_0$ there is a sequence of genera $g_j\to\infty$, all at least $g_0$, carrying such data, and for every binary encoding of $F$ one Turing machine outputs $t_j=2g_j+1$ and the list of the vectors $e_{P_a}$ within time polynomial in $t_j$.
--
--   This collects the algebraic-geometric input of Section 4: the Garcia–Stichtenoth tower, Riemann–Roch, and the determinantal independence. From it, the proof of Lemma 3.2 in Section 4.3 produces the direction sets $D=\{[e_{P_a}]\}$.
--
--   **Formalization Note** The curves, the tower and the Riemann–Roch spaces are not formalized; only their consequences in coordinates are stated. "For every $g_0$" reflects "discarding finitely many earlier tower levels" (p.17). Explicitness uses `HMBinPacking.OutputsWithin` and the encodings `encNat`, `encList`, `encFVec`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 4.1 and Section 4.1 (p.15), Section 4.2 and Lemma 4.5/Proposition 4.6 (pp.16–17), Section 4.3 (p.17); tower from Garcia–Stichtenoth (J. Number Theory 61 (1996)), algorithms from Guruswami–Xing (JACM 69 (2022))

import Mathlib
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

/-- **Section 4.1–4.2 and Proposition 4.6: evaluation data from the Garcia–Stichtenoth tower**
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
4. the `k × k` minors `p_J(x) = det (L_{ij}(x))_{i, j ∈ J}` are linearly independent functions
   `F^t → F` (Proposition 4.6);
5. the points (as vectors of `F^t`) are computable in time polynomial in `t` ([GX22], p.15).

Stated as: for every `g₀` there is a sequence of genera `g_j → ∞`, all `≥ g₀`, with vectors
`e_j : Fin ((q − 2) g_j) → F^{2g_j + 1}` and linear forms `L_j` with these properties, and for every
encoding `enc` of `F` one machine outputs `t_j = 2g_j + 1` and the list of the `e_j(a)` within
time polynomial in `t_j`.

**Formalization Note** The curve, the tower and the Riemann–Roch spaces are not formalized; this
statement records their consequences used in Section 4.3 in coordinates. "For every `g₀`" reflects
"discarding finitely many earlier tower levels" (p.17). -/
theorem tower_evaluation_data (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F]
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
          fun x : Fin (2 * g j + 1) → F =>
            (Matrix.of fun i l => L j i (J.1.orderEmbOfFin J.2 l) x).det)) ∧
      ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin M (encNat j)
            (encNat (2 * g j + 1) ++ encList (encFVec enc) (List.ofFn (e j)))
            (p.eval (2 * g j + 1)) := by sorry

end AbelianCayleyHDX
