-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_proposition_3_4
-- name    : ForestRoundingNSW.Rounding.proposition_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:31.743284+00:00
-- url     : https://prove2.me/theorems/fe184e87-1c9d-4071-9677-0b844b200720
-- title:
--   Proposition 3.4 — correlated forest rounding: E[ln max{v_i(S_i), B_i}] ≥ ln max{B_i, v_i(E_i), F_{f_i}(x_i)/C}, C = 2/(e ln 2)
-- statement:
--   Let $N$ be $n$ agents and $M$ $m$ items, $v_i:2^M\to\mathbb R_{\ge0}$ normalized monotone valuations, $G\subseteq M$, $B_i=\max_{j\in G}v_i(\{j\})$ ($0$ if $G=\emptyset$) and $N_+=\{i:B_i>0\}$. Let $(E_i)_{i\in N_+}$ be pairwise-disjoint subsets of $G$, $R=G\setminus\bigcup_{i\in N_+}E_i$ the remaining items, and $x\in P$ supported on agents in $N_+$ and items in $R$. For each $i\in N_+$ let $f_i$ be a normalized monotone submodular function on $R$ with $f_i(T)\le v_i(T)$ for every $T\subseteq R$, with multilinear extension $F_{f_i}$. Under the exact-evaluation convention there is a rounding algorithm returning pairwise-disjoint bundles $S_i\supseteq E_i$ such that
--   $$\mathbb E\big[\ln\max\{v_i(S_i),B_i\}\big]\;\ge\;\ln\max\Big\{B_i,\ v_i(E_i),\ \frac{F_{f_i}(x_i)}{C}\Big\}\qquad\text{for every }i\in N_+,\qquad C=\frac{2}{e\ln2}.$$
--   The algorithm uses polynomially many arithmetic operations and evaluations of the lower functions and their multilinear derivatives.
--
--   Formally: there are a universal constant $C_0$ and one admissible program on the randomized oracle real RAM, fixed before the instance, that reads $n,m,x,G$ and the $E_i$ and accesses the $f_i$ only through exact oracles for $f_i$, $F_{f_i}$ and $\partial_jF_{f_i}$ (restricted to $R$), such that on every instance every run halts within $C_0(n+m)^{C_0}+C_0$ steps; on every run the output bundles lie in $G$, are pairwise disjoint and satisfy $S_i\supseteq E_i$ for $i\in N_+$; and for every $i\in N_+$ the function $\nu\mapsto\ln\max\{v_i(S_i(\nu)),B_i\}$ is integrable under the uniform tape law and its integral is at least the right-hand side above.
--
--   This is the paper's titular result: the residual-rounding guarantee with geometric recovery factor $2/(e\ln2)$ that feeds the matching-rematching framework for submodular, XOS and subadditive Nash social welfare.
--
--   Differences from the source:
--   - generalization: G = M \ τ(N), the items left after the initial matching (§2.3) → any G ⊆ M; reason: the proposition's proof never uses how G was chosen; the paper's G is a special case
--   - generalization: valuations v_i : 2^M → ℚ≥0, normalized and monotone (§2.1) → real-valued v_i : Finset (Fin m) → ℝ, normalized and monotone; reason: contains the rational case; nonnegativity follows from normalized and monotone
--   - encoding: the family (E_i)_{i∈N₊} of pairwise-disjoint subsets of G → E : Fin n → Finset (Fin m) with E_i ⊆ G, pairwise disjoint, and E_i = ∅ for i ∉ N₊; reason: the same family extended by empty sets; G \ ⋃_i E_i is then the paper's remaining items
--   - encoding: f_i a normalized monotone submodular function on the remaining items R with f_i(T) ≤ v_i(T) for T ⊆ R, and F_{f_i} → f_i : Finset (Fin m) → ℝ through its restriction T ↦ f_i(T ∩ R): IsNMS of the restriction, f_i(T) ≤ v_i(T) for T ⊆ R, and F of the restriction; reason: the restriction is the function on 2^R; its multilinear extension is the multilinear extension over R
--   - reading: there is a rounding algorithm … using polynomially many arithmetic operations and evaluations of the lower functions and their multilinear derivatives (exact-evaluation convention) → ∃ universal C0 ∃ one admissible program on the randomized real RAM with rational literals, a uniform [0,1] tape and exact unit-cost oracles for f_i, F_{f_i}, ∂_j F_{f_i}; every run halts within C0·(n+m)^C0 + C0 steps; the program reads n, m, x, G and the E_i, never v_i, B_i or N₊; reason: the paper's algorithm model; the constant is fixed before the instance and the bound holds on every run
--   - reading: returning pairwise-disjoint bundles S_i ⊇ E_i → on every run: S_i ⊆ G for all agents, the bundles are pairwise disjoint over all agents, and E_i ⊆ S_i for i ∈ N₊; reason: §2.3(ii): the residual procedure allocates items of G with bundles pairwise disjoint on every outcome
--   - encoding: E[ln max{v_i(S_i), B_i}] → the integral against the uniform tape law, with integrability as a conclusion; reason: the expectation over the algorithm's randomness; integrability is claimed, not assumed
--   - encoding: agents N, items M and lower functions (f_i)_{i∈N₊} → agents Fin n, items Fin m, and a function f_i for every agent, constrained only for i ∈ N₊ (the program receives oracles for all n of them); reason: Lean convention; for i ∉ N₊ the row x_i is zero, and the program must work whatever f_i is there, so no instance of the source is lost
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 24, Proposition 3.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
import Definitions.Def_ForestRoundingNSW_Rounding_Allocation
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding
import Definitions.Def_ForestRoundingNSW_Rounding_Machine

open MeasureTheory NonmonotoneSubmod.Shared

namespace ForestRoundingNSW.Rounding

theorem proposition_3_4 :
    ∃ C0 : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (n m : ℕ) (v : Fin n → Finset (Fin m) → ℝ) (G : Finset (Fin m))
        (E : Fin n → Finset (Fin m)) (x : Fin n → Fin m → ℝ) (f : Fin n → Finset (Fin m) → ℝ),
        (∀ i, Normalized (v i) ∧ SetMonotone (v i)) →
        (∀ i, E i ⊆ G) → (∀ i, i ∉ Nplus v G → E i = ∅) →
        (∀ i i' : Fin n, i ≠ i' → Disjoint (E i) (E i')) →
        InP x → SupportedOn x (Nplus v G) (remaining G E) →
        (∀ i ∈ Nplus v G, IsNMS (restrict (f i) (remaining G E)) ∧
          ∀ T ⊆ remaining G E, f i T ≤ v i T) →
        (∀ ν : Tape, HaltsWithin P (fun i => restrict (f i) (remaining G E)) ν
            (initState n m x G E) (C0 * (n + m) ^ C0 + C0)) ∧
        (∀ ν : Tape,
            (∀ i, outBundles P (fun i => restrict (f i) (remaining G E)) (initState n m x G E) ν i
              ⊆ G) ∧
            (∀ i i' : Fin n, i ≠ i' →
              Disjoint (outBundles P (fun i => restrict (f i) (remaining G E))
                  (initState n m x G E) ν i)
                (outBundles P (fun i => restrict (f i) (remaining G E))
                  (initState n m x G E) ν i')) ∧
            ∀ i ∈ Nplus v G,
              E i ⊆ outBundles P (fun i => restrict (f i) (remaining G E))
                (initState n m x G E) ν i) ∧
        ∀ i ∈ Nplus v G,
          Integrable (fun ν : Tape => Real.log (max (v i (outBundles P
            (fun i => restrict (f i) (remaining G E)) (initState n m x G E) ν i)) (B v G i)))
            tapeLaw ∧
          Real.log (max (B v G i) (max (v i (E i))
              (F (restrict (f i) (remaining G E)) (x i) / C))) ≤
            ∫ ν : Tape, Real.log (max (v i (outBundles P
              (fun i => restrict (f i) (remaining G E)) (initState n m x G E) ν i)) (B v G i))
              ∂tapeLaw := by sorry

end ForestRoundingNSW.Rounding
