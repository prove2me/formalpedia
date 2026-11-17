-- Prove2me | solution 1 for thm_8_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:18:00.495503+00:00
-- url     : https://prove2.me/submissions/f6e07d7e-0beb-451a-893b-805fbd45a163

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

--  we need Dirac measure from example 3.4 in Chapter 3

/-
\begin{thmbox}{8.1}
Suppose $(\mathcal{X},\mathcal{F})$, $(\mathcal{Y},\mathcal{G})$, and
$(\Omega,\mathcal{H})$ are measurable spaces in which all singletons are
measurable. There is a unique measurable map
\[
h:(\Omega,\mathcal{H})\to (\mathcal{X}\times \mathcal{Y},\mathcal{F}\times \mathcal{G}),
\]
which yields a morphism from any coupling $(\Omega,\mathcal{H},\mu)$ of
$(\mathcal{X},\mathcal{F},P)$ and $(\mathcal{Y},\mathcal{G},Q)$ to
$(\mathcal{X}\times \mathcal{Y},\mathcal{F}\times \mathcal{G},h_{\#}\mu)$.
\end{thmbox}

\textit{Proof} We define the function $h:\Omega\to \mathcal{X}\times \mathcal{Y}$
for any element $\omega\in \Omega$ as $h(\omega)=(X(\omega),Y(\omega))$. This
function is measurable, meaning that for any measurable rectangle $E_1\times E_2$
in $\mathcal{X}\times \mathcal{Y}$, the inverse image $h^{-1}(E_1\times E_2)$ is
measurable. Specifically, $h^{-1}(E_1\times E_2)$ can be expressed as the
intersection of $X^{-1}(E_1)$ and $Y^{-1}(E_2)$, both of which are
$\mathcal{H}$-measurable sets.

Suppose $(\Omega,\mathcal{H},\mu)$ is a coupling of $(P,Q)$. By definition,
$X$ is a measurable map from $\Omega$ to $\mathcal{X}$ such that $X_{\#}\mu=P$,
and $Y$ is a measurable map from $\Omega$ to $\mathcal{Y}$ such that $Y_{\#}\mu=Q$.
\[
\Omega
\]
\[
\overset{X}{\swarrow} \qquad \downarrow h \qquad \overset{Y}{\searrow}
\]
\[
\mathcal{X} \qquad \xleftarrow{\pi_1} \mathcal{X}\times \mathcal{Y} \xrightarrow{\pi_2} \mathcal{Y}
\]

Consider the push-forward measure $h_{\#}\mu$ on $\mathcal{X}\times \mathcal{Y}$.
By the definition of the functions $\pi_1$ and $h$, we have $\pi_1^{-1}(E_1)=E_1\times \mathcal{Y}$ and
\[
h^{-1}(E_1\times \mathcal{Y})=X^{-1}(E_1).
\]

Therefore, for any $E_1\in \mathcal{F}$, we have $(\pi_1\circ h)^{-1}(E_1)=X^{-1}(E_1)$,
and thus
\[
\mu((\pi_1\circ h)^{-1}(E_1))=\mu(X^{-1}(E_1))=P(E_1).
\]

The last equality follows from the definition of coupling, which proves that the
$(\mu_1\circ h)_{\#}\mu=P$.

By a similar argument, we can show that $(\pi_2\circ h)_{\#}\mu=Q$.

To show the uniqueness of $h$, we fix an element $x\in \mathcal{X}$ and an element
$y\in \mathcal{Y}$. Since $\{x\}$ is a singleton, it is $\mathcal{F}$-measurable, and similarly, $\{y\}$ is $\mathcal{G}$-measurable. An element $\omega$ in the intersection of $X^{-1}(\{x\})$ and $Y^{-1}(\{y\})$ must be mapped to $(x,y)$ in $\mathcal{X}\times \mathcal{Y}$. To see this, we can set $P$ to be the Dirac measure concentrated at $x$ and $Q$ to be the Dirac measure concentrated at $y$ (see Example 3.3.4). The Dirac measure $\mu$ that is concentrated at $\omega$ is a coupling of the two Dirac measures $P$ and $Q$. In this case, defining $h(\omega)$ to be $(x,y)$ is the only way to satisfy the requirements $(\pi_1\circ h)_{\#}\mu=P$ and $(\pi_2\circ h)_{\#}\mu=Q$, thereby establishing the uniqueness of the function $h$. \hfill $\square$
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory


theorem solution
    {α β Ω : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass Ω]
    {μ : Measure Ω} {P : Measure α} {Q : Measure β}
    {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y)
    (hPX : Measure.map X μ = P) (hQY : Measure.map Y μ = Q) :
    ∃! h : Ω → α × β,
      Measurable h ∧
      Prod.fst ∘ h = X ∧
      Prod.snd ∘ h = Y ∧
      Measure.map Prod.fst (Measure.map h μ) = P ∧
      Measure.map Prod.snd (Measure.map h μ) = Q := by
  let h : Ω → α × β := fun ω => (X ω, Y ω)
  have hh : Measurable h := Measurable.prodMk hX hY
  refine ⟨h, ?_, ?_⟩
  · refine ⟨hh, rfl, rfl, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hh]
      change Measure.map X μ = P
      simpa [h, Function.comp] using hPX
    · rw [Measure.map_map measurable_snd hh]
      change Measure.map Y μ = Q
      exact hQY
  · intro h' hh'
    rcases hh' with ⟨hh'm, hh'fst, hh'snd, _, _⟩
    funext ω
    apply Prod.ext
    · simpa [Function.comp] using congrFun hh'fst ω
    · simpa [Function.comp] using congrFun hh'snd ω