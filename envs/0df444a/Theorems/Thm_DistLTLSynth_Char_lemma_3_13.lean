-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_3_13
-- name    : DistLTLSynth.Char.lemma_3_13
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T12:45:51.890947+00:00
-- url     : https://prove2.me/theorems/8256cd1c-a74b-466d-bf9a-21824c933c0e
-- title:
--   Symbolic compressed component-tree arena and universal bad-thread parity monitor (Lemma 3.13)
-- statement:
--   Let $I = (X_1, X_2, Y_1, Y_2, \mathrm{tokens})$ be a two-process distributed synthesis instance with input alphabets $[X_1], [X_2]$, output alphabets $[Y_1], [Y_2]$, and signal alphabet $\Sigma = [X_1] \times [X_2] \times \Gamma$, where $\Gamma$ is the set of directed communication graphs on $\{1, 2\}$. Fix a consensus block length $D = D_0 + 1 \ge 1$ and a compiled deterministic parity block automaton $(\mathcal{B}, Q_{\mathrm{live}})$ with state set $Q_{\mathcal{B}}$, priority map $p_{\mathcal{B}} : Q_{\mathcal{B}} \to \{0, \dots, K\}$, retraction bound $B_{\mathrm{red}} = (1 + |Q_{\mathcal{B}}|)^{|\Sigma|^D} \cdot |\Sigma|^D$, and full extension bound $B_{\mathrm{full}} = B_{\mathrm{red}} \cdot |\Sigma|^D$.
--
--   Write $\mathcal{P}(I, D, \mathcal{B})$ for the finite set of compressed symbolic positions $\pi = (k, \equiv_1, \equiv_2, q)$ consisting of a size $1 \le k \le B_{\mathrm{full}}$, equivalence tables $\equiv_1, \equiv_2$ on $\{0, \dots, k-1\}$, and a state labeling $q : \{0, \dots, k-1\} \to Q_{\mathcal{B}}$, and write $\mathcal{A}(\pi)$ for the finite set of admissible symbolic compression actions $\alpha = (r, o_1, o_2)$ consisting of an idempotent retraction $r : \{0, \dots, k-1\} \to \{0, \dots, k-1\}$ with $|\mathrm{Fix}(r)| \le B_{\mathrm{red}}$ preserving $q$, $\equiv_1$, and $\equiv_2$, together with view-coherent $D$-round local output tables $o_1, o_2$. For each admissible pair $(\pi, \alpha)$, let $S(\pi, \alpha) \subseteq \mathrm{Fix}(r) \times \Sigma^D \times Q_{\mathcal{B}}$ be the set of $Q_{\mathrm{live}}$-reaching $D$-round extensions and $C_0(\pi, \alpha), \dots, C_{m-1}(\pi, \alpha)$ its partition into connected components under combined $1$- and $2$-indistinguishability.
--
--   Then the symbolic arena, formula parser, and deterministic parity branch monitor $\mathcal{D}_{I, D, \mathcal{B}}$ satisfy the following properties:
--
--   1. **Prefix-Polish LTL parsing and semantic instantiation:** Testing whether $\mathrm{tokens} \in \mathrm{Token}^*$ parses to a unique linear temporal logic formula $\varphi$ is primitive recursive, and for every message adversary $A \subseteq \Gamma^\omega$ and distributed algorithm $f$, realizing the typed instantiation $\varphi_I$ of $\varphi$ under $A$ is equivalent to realizing the trace language $\mathcal{L}_I(\varphi)$.
--   2. **Primitive-recursive symbolic arena and component decomposition:** Enumerating valid symbolic position-action labels $\Lambda = \{(\pi, \alpha) : \pi \in \mathcal{P}(I, D, \mathcal{B}),\, \alpha \in \mathcal{A}(\pi)\}$, single-block state transitions, live extension sets $S(\pi, \alpha)$ (of cardinality at most $B_{\mathrm{full}}$), connected components $C_d(\pi, \alpha)$ ($m \le B_{\mathrm{full}}$), and child symbolic positions $\tilde{\pi}_d$ is primitive recursive; moreover, incremental view-equivalence propagation across finite signal blocks $w_1, w_2 \in \Sigma^*$ tracks exact local view equality $\mathrm{view}_p(h_1 \cdot w_1) = \mathrm{view}_p(h_2 \cdot w_2)$ for both processes $p \in \{1, 2\}$.
--   3. **Universal bad-thread branch acceptance:** The tree specification $\mathcal{T}(I, D, \mathcal{B})$ is primitive recursive, enforces root initialization and child position matching along every valid branch, and its deterministic parity branch automaton $\mathcal{D}_{I, D, \mathcal{B}}$ accepts an infinite branch $(\ell_n, d_n)_{n \ge 0}$ if and only if no infinite folded edge thread has odd minimum infinitely-occurring priority:
--
--   $$
--   \mathcal{D}_{I, D, \mathcal{B}} \text{ accepts } (\ell_n, d_n)_{n \ge 0} \iff \neg \exists (i_n, p_n)_{n \ge 0} \in \{0, \dots, B_{\mathrm{full}} - 1\}^\omega \times \{0, \dots, K\}^\omega,\quad i_0 = 0 \;\land\; \bigl(\forall n \ge 0,\, (i_n, p_n, i_{n+1}) \in \Delta(\ell_n, d_n)\bigr) \;\land\; \liminf_{n \to \infty} p_n \equiv 1 \pmod{2}.
--   $$
--
--   This result provides the computable finite-alphabet regular tree parity game representation of compressed component trees required to decide realizability and synthesize finite-state controllers in distributed LTL synthesis.
--
--   **Formalization Note** In Lean, the automaton compilation and tree-game solver primitives from earlier subsections are bundled in a record `Thm34Engine`, symbolic contexts are represented as tuples `SymCtx` storing $(I, D - 1, \mathcal{B}, Q_{\mathrm{live}})$, and $1$-based label indices reserve $0$ as an absorbing padding symbol for unused arity directions.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), Section 3.3, p. 16 (PDF 17), Lemma 3.13

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine
import Definitions.Def_DistLTLSynth_Char_SymbolicArena

set_option autoImplicit false

namespace DistLTLSynth.Char

theorem lemma_3_13 :
    (Primrec parseOk) ∧
    (∀ ts : List Token, parseOk ts = true ↔ ∃ φ, parse ts = some φ) ∧
    (∀ (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) (A : Set (ℕ → CommGraph)) (f : Algorithm I.X1 I.X2 I.Y1 I.Y2),
      FRealizes f A (instFormulaOf I φ) ↔ RealizesLang f A (I.Lang φ)) ∧
    (Primrec validSymLabels) ∧
    (∀ c : SymCtx, (validSymLabels c).Nodup) ∧
    (∀ (c : SymCtx) (pa : SymPosCode × SymActCode),
      pa ∈ validSymLabels c ↔
        pa.1 ∈ allSymPos c ∧ pa.2 ∈ allSymActsFor c pa.1 ∧ actValid c pa.1 pa.2 = true) ∧
    (∀ E : Thm34Engine, Primrec (symNextStatePacked E)) ∧
    (∀ E : Thm34Engine, Primrec (symComponentsPacked E)) ∧
    (∀ E : Thm34Engine, Primrec (buildTreeSpec E)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx) (a : Fin ((buildTreeSpec E c).2.1 + 1)),
      tsRootOk (buildTreeSpec E c) a =
        if a.val = 0 then false
        else decide (((validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))).1 = initSymPos)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx) (a : Fin ((buildTreeSpec E c).2.1 + 1))
      (d : Fin ((buildTreeSpec E c).1 + 1)) (a' : Fin ((buildTreeSpec E c).2.1 + 1)),
      tsChildOk (buildTreeSpec E c) a d a' =
        if a.val = 0 then decide (a'.val = 0)
        else
          let pa := (validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))
          let comps := symComponents E c pa.1 pa.2
          if d.val < comps.length then
            if a'.val = 0 then false
            else
              let pa' := (validSymLabels c).getD (a'.val - 1) (initSymPos, ([], [], []))
              decide (pa'.1 = childSymPos (ctxI c) pa.1 (comps.getD d.val []))
          else decide (a'.val = 0)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx)
      (ad : ℕ → Fin ((buildTreeSpec E c).2.1 + 1) × Fin ((buildTreeSpec E c).1 + 1)),
      (tsDPA (buildTreeSpec E c)).Accepts ad ↔
        ¬ ∃ (iSeq : ℕ → Fin (ctxBFull c)) (pSeq : ℕ → Fin (maxList (ctxBCode c).2.2 + 1)),
          (iSeq 0).val = 0 ∧
          (∀ n, edgeStepOk E c (validSymLabels c) (ad n).1.val (ad n).2.val
            (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true) ∧
          OddParityCond (fun n => (pSeq n).val)) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode) (e : SymExtElem),
      e ∈ symLiveExts E ctx pos act ↔
        e.1 ∈ fixedIdxs pos act ∧
        e.2.1 ∈ fullBlocks (ctxI ctx) (ctxD ctx) ∧
        e.2.2 = symNextState E ctx pos act e.1 e.2.1 ∧
        (ctxLive ctx).getD e.2.2 false = true) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode),
      (fixedIdxs pos act).length ≤ ctxBRed ctx →
      (symLiveExts E ctx pos act).Nodup ∧ (symLiveExts E ctx pos act).length ≤ ctxBFull ctx) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode),
      (fixedIdxs pos act).length ≤ ctxBRed ctx →
      let S := symLiveExts E ctx pos act
      let comps := symComponents E ctx pos act
      comps.length ≤ ctxBFull ctx ∧
      ∀ (d : ℕ) (hd : d < comps.length),
        let comp := comps[d]'hd
        1 ≤ comp.length ∧ comp.length ≤ ctxBFull ctx ∧ comp.Nodup ∧
        (∀ e ∈ comp, e ∈ S) ∧
        ((∀ a ∈ S, ∀ b ∈ S, symExtAdj (ctxI ctx) pos a b = symExtAdj (ctxI ctx) pos b a) →
          ∀ j1 j2 : Fin comp.length,
            Relation.ReflTransGen
              (fun x y : Fin comp.length => symExtAdj (ctxI ctx) pos comp[x] comp[y] = true) j1 j2)) ∧
    (∀ (I : Instance) (pos : SymPosCode) (comp : List SymExtElem),
      let pos' := childSymPos I pos comp
      pos'.1 = comp.length ∧
      (∀ a (ha : a < comp.length) b (hb : b < comp.length),
        eq1At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).1) ∧
      (∀ a (ha : a < comp.length) b (hb : b < comp.length),
        eq2At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).2) ∧
      (∀ a (ha : a < comp.length), stateAt pos' a = (comp[a]'ha).2.2)) ∧
    (∀ (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)}, h1.length = h2.length →
      ∀ (w1 w2 : List ℕ),
        extEqFrom I (decide (view1 h1 = view1 h2)) (decide (view2 h1 = view2 h2)) w1 w2 =
          (decide (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2)),
           decide (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2)))) ∧
    (∀ (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)}, h1.length = h2.length →
      ∀ {b1 b2 : Bool}, (view1 h1 = view1 h2 → b1 = true) → (view2 h1 = view2 h2 → b2 = true) →
      ∀ (w1 w2 : List ℕ),
        (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).1 = true) ∧
          (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).2 = true)) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) {i : ℕ}, i < S.length →
      ∀ y : ℕ,
        y ∈ compIdxOf inh S adj i ↔
          y < S.length ∧
            Relation.ReflTransGen
              (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i y) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) {i : ℕ}, i < S.length →
      (compIdxOf inh S adj i).Nodup ∧ i ∈ compIdxOf inh S adj i ∧
        (compIdxOf inh S adj i).length ≤ S.length ∧
        ∀ y ∈ compIdxOf inh S adj i, y < S.length) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool),
      (∀ a < S.length, ∀ b < S.length,
        adj (S.getD a inh) (S.getD b inh) = adj (S.getD b inh) (S.getD a inh)) →
      ∀ {i j : ℕ}, i < S.length → j < S.length →
      Relation.ReflTransGen
        (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i j →
      compIdxOf inh S adj i = compIdxOf inh S adj j) := by sorry

end DistLTLSynth.Char
