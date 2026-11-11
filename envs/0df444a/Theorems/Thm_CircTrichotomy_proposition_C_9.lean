-- Prove2me | Theorems.Thm_CircTrichotomy_proposition_C_9
-- name    : CircTrichotomy.proposition_C_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:56.204147+00:00
-- url     : https://prove2.me/theorems/0a7b97f4-0a55-4ba6-8f37-3201af4aea58
-- title:
--   Proposition C.9 — separating $n-1$ pairs needs $n-1$ gates
-- statement:
--   **Proposition C.9.** Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language with $\eta_L\notin\mathbf X$. Let $s$ be the stability index of $\eta_L$, let $k\ge1$ be a multiple of $s$, let $u,v,w\in\Sigma^k$ with $\eta_L(u)$, $\eta_L(w)$ idempotent and $j_0\in[0,k-1]$ such that
--   $$\eta_L\bigl(u\,v[j_0\leftarrow u_{j_0}]\,w\bigr)\ne\eta_L\bigl(u\,v[j_0\leftarrow w_{j_0}]\,w\bigr),$$
--   and put $v'=v[j_0\leftarrow u_{j_0}]$, $v''=v[j_0\leftarrow w_{j_0}]$, $x_{n,i}=u^iv'w^{n-i}$, $y_{n,i}=u^iv''w^{n-i}$. Then for each $n\ge2$, every single-output $k(n+1)$-circuit $C$ that separates all pairs $(x_{n,1},y_{n,1}),\dots,(x_{n,n-1},y_{n,n-1})$ satisfies
--   $$|C|\ge n-1.$$
--
--   It gives $c(L)\in\Omega(n)$ in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
--   - encoding: the data L, u, v, w, k, j₀ fixed at the start of §C.2 (p.45) → hypotheses of the theorem, including η_L ∉ X and (180); reason: Proposition C.9 is stated under these standing assumptions
--   - encoding: uⁱ and w^{n−i} → FanInSemigroup.ppow u i and FanInSemigroup.ppow w (n − i), exponents in ℕ+; reason: positive powers in the free semigroup (published definition FanInSemigroup_wordProd); i ≥ 1 and n − i ≥ 1 for i ∈ [1, n − 1]
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition C.9, p.46 (standing assumptions p.45)

import Mathlib
import Definitions.Def_CircTrichotomy_wordToList
import Definitions.Def_FanInSemigroup_wordProd
import Definitions.Def_CircTrichotomy_syntMorphism
import Definitions.Def_CircTrichotomy_IsStabilityIndex
import Definitions.Def_CircTrichotomy_InX
import Definitions.Def_CircTrichotomy_Separates

set_option autoImplicit false

namespace CircTrichotomy

/-- **Proposition C.9 (linear lower bound by gate counting)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition C.9, p.46, under the
standing assumptions of §C.2, p.45): "For the rest of this section fix a regular language L such
that η_L is not in X. By Lemma C.1 there exist words u = u₀ … u_{k−1}, v = v₀ … v_{k−1}, and
w = w₀ … w_{k−1}, where k ∈ ℕ>0 is a multiple of the stability index of η_L, j₀ ∈ [0, k − 1], u and
w are idempotents and moreover uv[j₀ ← u_{j₀}]w ≠_{η_L} uv[j₀ ← w_{j₀}]w, (180) … In the following
let v′ = v[j₀ ← u_{j₀}] and v″ = v[j₀ ← w_{j₀}] … for each n ≥ 2 and each i ∈ [1, n − 1] we define the
following words from Σ^{k(n+1)}: x_{n,i} = uⁱv′w^{n−i} ∈ K (182), y_{n,i} = uⁱv″w^{n−i} ∉ K (183). …
Proposition C.9. For each n ≥ 2 each k(n + 1)-circuit C that separates all of the n − 1 pairs of
words (x_{n,1}, y_{n,1}), …, (x_{n,n−1}, y_{n,n−1}), satisfies |C| ≥ n − 1."

**Formalization Note** The standing assumptions of §C.2 are hypotheses. `uⁱ` and `w^{n−i}` are the
positive powers `FanInSemigroup.ppow u i` and `FanInSemigroup.ppow w (n − i)` (`i ≥ 1`, `n − i ≥ 1`;
published definition `FanInSemigroup_wordProd`). `C` is a single-output
`k(n + 1)`-circuit; "separates" is Definition C.7 (`Separates`). -/
theorem proposition_C_9 {α : Type} [Fintype α] [Nonempty α] (L : Language α)
    (hreg : L.IsRegular) (hL : [] ∉ L) (hX : ¬ InX (syntMorphism L)) (s k : ℕ)
    (hs : IsStabilityIndex (syntMorphism L) s) (hk : 0 < k) (hsk : s ∣ k)
    (u v w : FreeSemigroup α) (hu : u.length = k) (hv : v.length = k) (hw : w.length = k)
    (j₀ : ℕ) (hj₀ : j₀ < k)
    (hu_idem : syntMorphism L u * syntMorphism L u = syntMorphism L u)
    (hw_idem : syntMorphism L w * syntMorphism L w = syntMorphism L w)
    (h180 : syntMorphism L (u * setAt v j₀ (letterAt u j₀) * w) ≠
      syntMorphism L (u * setAt v j₀ (letterAt w j₀) * w))
    (n : ℕ) (hn : 2 ≤ n) (C : Circuit α (k * (n + 1)) 1)
    (hsep : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n - 1),
      Separates C
        (wordToList (FanInSemigroup.ppow u ⟨i, hi⟩ * setAt v j₀ (letterAt u j₀) *
          FanInSemigroup.ppow w ⟨n - i, by omega⟩))
        (wordToList (FanInSemigroup.ppow u ⟨i, hi⟩ * setAt v j₀ (letterAt w j₀) *
          FanInSemigroup.ppow w ⟨n - i, by omega⟩))) :
    n - 1 ≤ C.size := by sorry

end CircTrichotomy
