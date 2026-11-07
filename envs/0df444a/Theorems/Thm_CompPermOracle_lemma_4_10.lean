-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_10
-- name    : CompPermOracle.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:50.626225+00:00
-- url     : https://prove2.me/theorems/b7033877-dc21-40b4-88b3-958238fb5255
-- title:
--   Lemma 4.10 — frame identities, zero-sum relations on $K_r$ and the POVM
-- statement:
--   For every $r$,
--   $$
--   \Gamma_rV_r=I_{\mathcal H_r},\quad V_r^\dagger V_r=G_r^{-1},\quad\|V_r\|\le1,\qquad \tilde V_r^\dagger\tilde V_r=I_{\mathcal H_r},\quad\tilde V_r\tilde V_r^\dagger=\Pi_{K_r},\quad E_r\tilde V_r=G^{1/2}_r.
--   $$
--   For every $a\in K_r$,
--   $$
--   \sum_{b\notin\mathrm{im}(h)}a_{h[u\mapsto b]}=0,\qquad\sum_{u\notin\mathrm{dom}(h)}a_{h[u\mapsto b]}=0,\qquad E_ra=\Gamma_ra\in\mathcal H_r,
--   $$
--   the first for $h\in\mathcal I_{r-1}$ and $u\notin\mathrm{dom}(h)$, the second for $h\in\mathcal I_{r-1}$ and $b\notin\mathrm{im}(h)$, both vacuous for $r=0$. In particular $E_rV_r=I_{\mathcal H_r}$ and $\Pi_{K_r}=V_r\Gamma_r$. Finally, the operators
--   $$
--   G_r^{-1/2}\Pi_r|T_f\rangle\langle T_f|\Pi_rG_r^{-1/2},\qquad f\in\mathcal I_r,
--   $$
--   form a POVM on $\mathcal H_r$, whose coherent measurement is $\tilde V_r$.
--
--   These identities say that $\tilde V$ is an isometry and describe the compressed states in its range.
--
--   Differences from the source:
--   - reading: the operators (41) form a POVM on $\mathcal H_r$, whose coherent measurement is $\tilde V_r$ → each operator is positive, they sum to $\Pi_r$, and $\langle f|\tilde V_r\psi\rangle=\langle G_r^{-1/2}\Pi_rT_f,\psi\rangle$ for $f\in\mathcal I_r$, $\psi\in\mathcal H_r$; reason: the amplitude of outcome $f$ is the inner product with the measurement vector whose rank-one operator is the POVM element
--   - reading: $I_{\mathcal H_r}$ → the claim for $\psi\in\mathcal H_r$ in (37), (40); equality with $\Pi_r$ as operators on $\mathcal P$ in (38); reason: the operators vanish off $\mathcal H_r$
--   - encoding: $G_r^{-1}$, $G_r^{-1/2}$, $h\in\mathcal I_{r-1}$ → inverses on $\mathcal H_r$ extended by $0$ (functional calculus); `size h + 1 = r`; reason: the same operators; no $h$ exists at $r=0$
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.10, p.18

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels

namespace CompPermOracle

/-- Lemma 4.10 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.18): the frame identities (37), (38), the zero-sum relations
and the range statement (39), the consequences (40), and the POVM (41).

**Formalization Note.** "For every `r`" is taken literally: for `r ≥ N`, `ℋ_r` is `0` (or `G_0 = I` at
`N = 0`), and every clause still holds. `I_{ℋ_r}` in (37), (40) is the identity on `ℋ_r`: the claim for
`ψ ∈ ℋ_r`, or the equality with `Π_r` as operators on `𝒫` for (38). `G_r^{−1}`, `G_r^{−1/2}` are the
inverses on `ℋ_r` extended by `0`. In (39), `h ∈ ℐ_{r−1}` is `size h + 1 = r`, which is vacuous at `r = 0`,
as in the source. In (41), "form a POVM on `ℋ_r`" is: each operator is positive and they sum to `Π_r`.
"Whose coherent measurement is `Ṽ_r`" is read as `⟨f|Ṽ_r ψ⟩ = ⟨G_r^{−1/2} Π_r T_f, ψ⟩` for `f ∈ ℐ_r`,
`ψ ∈ ℋ_r`: the amplitude of outcome `f` is the inner product of `ψ` with the measurement vector whose
rank-one operator is the POVM element. -/
theorem lemma_4_10 {N r : ℕ} :
    (∀ ψ ∈ Hlevel N r, Gam N r (Vr N r ψ) = ψ) ∧
    (ContinuousLinearMap.adjoint (Vr N r)).comp (Vr N r) = GramInv N r ∧
    ‖Vr N r‖ ≤ 1 ∧
    (ContinuousLinearMap.adjoint (Vtr N r)).comp (Vtr N r) = ProjLevel N r ∧
    (Vtr N r).comp (ContinuousLinearMap.adjoint (Vtr N r)) = ProjK N r ∧
    (synth N r).comp (Vtr N r) = GramSqrt N r ∧
    (∀ a ∈ Kr N r,
      (∀ h : PartialPerm N, size h + 1 = r → ∀ u, NotInDom h u →
        ∑ b ∈ freeIm h, a (addPair h u b) = 0) ∧
      (∀ h : PartialPerm N, size h + 1 = r → ∀ b, NotInIm h b →
        ∑ u ∈ freeDom h, a (addPair h u b) = 0) ∧
      synth N r a = Gam N r a ∧ Gam N r a ∈ Hlevel N r) ∧
    (∀ ψ ∈ Hlevel N r, synth N r (Vr N r ψ) = ψ) ∧
    ProjK N r = (Vr N r).comp (Gam N r) ∧
    (∀ f ∈ levelSet N r,
      ((GramInvSqrt N r).comp ((ProjLevel N r).comp
        ((ketBra (completion f) (completion f)).comp
          ((ProjLevel N r).comp (GramInvSqrt N r))))).IsPositive) ∧
    (∑ f ∈ levelSet N r,
      (GramInvSqrt N r).comp ((ProjLevel N r).comp
        ((ketBra (completion f) (completion f)).comp
          ((ProjLevel N r).comp (GramInvSqrt N r))))) = ProjLevel N r ∧
    (∀ f ∈ levelSet N r, ∀ ψ ∈ Hlevel N r,
      Vtr N r ψ f = inner ℂ (GramInvSqrt N r (ProjLevel N r (completion f))) ψ) := by sorry

end CompPermOracle
